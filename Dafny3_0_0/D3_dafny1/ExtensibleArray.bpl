// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy -print:./ExtensibleArray.bpl

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

const unique class._module.ExtensibleArray?: ClassName;

function Tclass._module.ExtensibleArray?(Ty) : Ty;

const unique Tagclass._module.ExtensibleArray?: TyTag;

// Tclass._module.ExtensibleArray? Tag
axiom (forall _module.ExtensibleArray$T: Ty :: 
  { Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  Tag(Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T))
       == Tagclass._module.ExtensibleArray?
     && TagFamily(Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T))
       == tytagFamily$ExtensibleArray);

// Tclass._module.ExtensibleArray? injectivity 0
axiom (forall _module.ExtensibleArray$T: Ty :: 
  { Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  Tclass._module.ExtensibleArray?_0(Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T))
     == _module.ExtensibleArray$T);

function Tclass._module.ExtensibleArray?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.ExtensibleArray?
axiom (forall _module.ExtensibleArray$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)) } 
  $IsBox(bx, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)));

// ExtensibleArray: Class $Is
axiom (forall _module.ExtensibleArray$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)) } 
  $Is($o, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T))
     <==> $o == null
       || dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T));

// ExtensibleArray: Class $IsAlloc
axiom (forall _module.ExtensibleArray$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T), $h) } 
  $IsAlloc($o, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.ExtensibleArray.Contents) == 0
   && FieldOfDecl(class._module.ExtensibleArray?, field$Contents)
     == _module.ExtensibleArray.Contents
   && $IsGhostField(_module.ExtensibleArray.Contents);

const _module.ExtensibleArray.Contents: Field (Seq Box);

// ExtensibleArray.Contents: Type axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.Contents), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
     ==> $Is(read($h, $o, _module.ExtensibleArray.Contents), TSeq(_module.ExtensibleArray$T)));

// ExtensibleArray.Contents: Allocation axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.Contents), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ExtensibleArray.Contents), 
      TSeq(_module.ExtensibleArray$T), 
      $h));

axiom FDim(_module.ExtensibleArray.Repr) == 0
   && FieldOfDecl(class._module.ExtensibleArray?, field$Repr)
     == _module.ExtensibleArray.Repr
   && $IsGhostField(_module.ExtensibleArray.Repr);

const _module.ExtensibleArray.Repr: Field (Set Box);

// ExtensibleArray.Repr: Type axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.Repr), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
     ==> $Is(read($h, $o, _module.ExtensibleArray.Repr), TSet(Tclass._System.object?())));

// ExtensibleArray.Repr: Allocation axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.Repr), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ExtensibleArray.Repr), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.ExtensibleArray.elements) == 0
   && FieldOfDecl(class._module.ExtensibleArray?, field$elements)
     == _module.ExtensibleArray.elements
   && !$IsGhostField(_module.ExtensibleArray.elements);

const _module.ExtensibleArray.elements: Field ref;

// ExtensibleArray.elements: Type axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.elements), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
     ==> $Is(read($h, $o, _module.ExtensibleArray.elements), 
      Tclass._System.array?(_module.ExtensibleArray$T)));

// ExtensibleArray.elements: Allocation axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.elements), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ExtensibleArray.elements), 
      Tclass._System.array?(_module.ExtensibleArray$T), 
      $h));

axiom FDim(_module.ExtensibleArray.more) == 0
   && FieldOfDecl(class._module.ExtensibleArray?, field$more)
     == _module.ExtensibleArray.more
   && !$IsGhostField(_module.ExtensibleArray.more);

const _module.ExtensibleArray.more: Field ref;

// ExtensibleArray.more: Type axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.more), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
     ==> $Is(read($h, $o, _module.ExtensibleArray.more), 
      Tclass._module.ExtensibleArray?(Tclass._System.array?(_module.ExtensibleArray$T))));

// ExtensibleArray.more: Allocation axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.more), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ExtensibleArray.more), 
      Tclass._module.ExtensibleArray?(Tclass._System.array?(_module.ExtensibleArray$T)), 
      $h));

axiom FDim(_module.ExtensibleArray.length) == 0
   && FieldOfDecl(class._module.ExtensibleArray?, field$length)
     == _module.ExtensibleArray.length
   && !$IsGhostField(_module.ExtensibleArray.length);

const _module.ExtensibleArray.length: Field int;

// ExtensibleArray.length: Type axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.length), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
     ==> $Is(read($h, $o, _module.ExtensibleArray.length), TInt));

// ExtensibleArray.length: Allocation axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.length), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ExtensibleArray.length), TInt, $h));

axiom FDim(_module.ExtensibleArray.M) == 0
   && FieldOfDecl(class._module.ExtensibleArray?, field$M)
     == _module.ExtensibleArray.M
   && !$IsGhostField(_module.ExtensibleArray.M);

const _module.ExtensibleArray.M: Field int;

// ExtensibleArray.M: Type axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.M), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
     ==> $Is(read($h, $o, _module.ExtensibleArray.M), TInt));

// ExtensibleArray.M: Allocation axiom
axiom (forall _module.ExtensibleArray$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ExtensibleArray.M), Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ExtensibleArray.M), TInt, $h));

// function declaration for _module.ExtensibleArray.Valid
function _module.ExtensibleArray.Valid(_module.ExtensibleArray$T: Ty, $ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T: Ty, $heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall _module.ExtensibleArray$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($ly), $Heap, this) } 
  _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($ly), $Heap, this)
     == _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $ly, $Heap, this));

// fuel synonym axiom
axiom (forall _module.ExtensibleArray$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, AsFuelBottom($ly), $Heap, this) } 
  _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $ly, $Heap, this)
     == _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LZ, $Heap, this));

function Tclass._module.ExtensibleArray(Ty) : Ty;

const unique Tagclass._module.ExtensibleArray: TyTag;

// Tclass._module.ExtensibleArray Tag
axiom (forall _module.ExtensibleArray$T: Ty :: 
  { Tclass._module.ExtensibleArray(_module.ExtensibleArray$T) } 
  Tag(Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
       == Tagclass._module.ExtensibleArray
     && TagFamily(Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
       == tytagFamily$ExtensibleArray);

// Tclass._module.ExtensibleArray injectivity 0
axiom (forall _module.ExtensibleArray$T: Ty :: 
  { Tclass._module.ExtensibleArray(_module.ExtensibleArray$T) } 
  Tclass._module.ExtensibleArray_0(Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
     == _module.ExtensibleArray$T);

function Tclass._module.ExtensibleArray_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.ExtensibleArray
axiom (forall _module.ExtensibleArray$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T)) } 
  $IsBox(bx, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T)));

// frame axiom for _module.ExtensibleArray.Valid
axiom (forall _module.ExtensibleArray$T: Ty, $ly: LayerType, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $ly, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.ExtensibleArray.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $ly, $h0, this)
       == _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $ly, $h1, this));

// consequence axiom for _module.ExtensibleArray.Valid
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.ExtensibleArray$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $ly, $Heap, this) } 
    _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
           && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap))
       ==> 
      _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $ly, $Heap, this)
       ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]);

function _module.ExtensibleArray.Valid#requires(Ty, LayerType, Heap, ref) : bool;

// #requires axiom for _module.ExtensibleArray.Valid
axiom (forall _module.ExtensibleArray$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.ExtensibleArray.Valid#requires(_module.ExtensibleArray$T, $ly, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
       && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap)
     ==> _module.ExtensibleArray.Valid#requires(_module.ExtensibleArray$T, $ly, $Heap, this)
       == true);

// definition axiom for _module.ExtensibleArray.Valid (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.ExtensibleArray$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
           && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap))
       ==> (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           ==> 
          !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           ==> 
          (
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))])
           ==> 
          read($Heap, this, _module.ExtensibleArray.more) != null
           ==> 
          read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
           ==> 
          Set#Subset(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Repr), 
            read($Heap, this, _module.ExtensibleArray.Repr))
           ==> 
          !read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr)[$Box(this)]
           ==> 
          !read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
           ==> _module.ExtensibleArray.Valid#canCall(Tclass._System.array?(_module.ExtensibleArray$T), 
            $Heap, 
            read($Heap, this, _module.ExtensibleArray.more)))
         && _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($ly), $Heap, this)
           == (
            read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
             && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
             && ((
                read($Heap, this, _module.ExtensibleArray.elements) == null
                 && read($Heap, this, _module.ExtensibleArray.more) == null
                 && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
               || (
                read($Heap, this, _module.ExtensibleArray.elements) != null
                 && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                   == LitInt(256)
                 && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
             && (read($Heap, this, _module.ExtensibleArray.more) != null
               ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
                 && Set#Subset(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr), 
                  read($Heap, this, _module.ExtensibleArray.Repr))
                 && !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[$Box(this)]
                 && !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
                 && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                  $ly, 
                  $Heap, 
                  read($Heap, this, _module.ExtensibleArray.more))
                 && Seq#Length(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Contents))
                   != 0
                 && (forall j#0: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#0)): ref } 
                  true
                     ==> (LitInt(0) <= j#0
                           && j#0
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#0)): ref
                           != null)
                       && (LitInt(0) <= j#0
                           && j#0
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#0)): ref)
                           == LitInt(256))
                       && (LitInt(0) <= j#0
                           && j#0
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)])
                       && (LitInt(0) <= j#0
                           && j#0
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> !read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)])
                       && (LitInt(0) <= j#0
                           && j#0
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#0)): ref
                           != read($Heap, this, _module.ExtensibleArray.elements))
                       && (LitInt(0) <= j#0
                           && j#0
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> (forall k#0: int :: 
                          { $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#0)): ref } 
                          true
                             ==> 
                            LitInt(0) <= k#0
                               && k#0
                                 < Seq#Length(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents))
                               && k#0 != j#0
                             ==> $Unbox(Seq#Index(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents), 
                                  j#0)): ref
                               != $Unbox(Seq#Index(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents), 
                                  k#0)): ref))))
             && read($Heap, this, _module.ExtensibleArray.M)
               == (if read($Heap, this, _module.ExtensibleArray.more) == null
                 then 0
                 else Mul(LitInt(256), 
                  Seq#Length(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Contents))))
             && 
            LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
             && read($Heap, this, _module.ExtensibleArray.length)
               <= read($Heap, this, _module.ExtensibleArray.M) + 256
             && (read($Heap, this, _module.ExtensibleArray.more) != null
               ==> read($Heap, this, _module.ExtensibleArray.M)
                 < read($Heap, this, _module.ExtensibleArray.length))
             && read($Heap, this, _module.ExtensibleArray.length)
               == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
             && (forall i#0: int :: 
              { $Unbox(Seq#Index(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Contents), 
                    Div(i#0, 256))): ref } 
                { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0) } 
              true
                 ==> 
                LitInt(0) <= i#0 && i#0 < read($Heap, this, _module.ExtensibleArray.M)
                 ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0)
                   == read($Heap, 
                    $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        Div(i#0, LitInt(256)))): ref, 
                    IndexField(Mod(i#0, LitInt(256)))))
             && (forall i#1: int :: 
              { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1) } 
              true
                 ==> 
                read($Heap, this, _module.ExtensibleArray.M) <= i#1
                   && i#1 < read($Heap, this, _module.ExtensibleArray.length)
                 ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1)
                   == read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.elements), 
                    IndexField(i#1 - read($Heap, this, _module.ExtensibleArray.M))))));

procedure CheckWellformed$$_module.ExtensibleArray.Valid(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
     ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];



implementation CheckWellformed$$_module.ExtensibleArray.Valid(_module.ExtensibleArray$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var j#1: int;
  var k#1: int;
  var i#2: int;
  var i#3: int;
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
  var b$reqreads#56: bool;
  var b$reqreads#57: bool;
  var b$reqreads#58: bool;
  var b$reqreads#59: bool;
  var b$reqreads#60: bool;
  var b$reqreads#61: bool;
  var b$reqreads#62: bool;
  var b$reqreads#63: bool;
  var b$reqreads#64: bool;
  var b$reqreads#65: bool;
  var b$reqreads#66: bool;
  var b$reqreads#67: bool;
  var b$reqreads#68: bool;
  var b$reqreads#69: bool;

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
    b$reqreads#56 := true;
    b$reqreads#57 := true;
    b$reqreads#58 := true;
    b$reqreads#59 := true;
    b$reqreads#60 := true;
    b$reqreads#61 := true;
    b$reqreads#62 := true;
    b$reqreads#63 := true;
    b$reqreads#64 := true;
    b$reqreads#65 := true;
    b$reqreads#66 := true;
    b$reqreads#67 := true;
    b$reqreads#68 := true;
    b$reqreads#69 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(13,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.ExtensibleArray.Repr];
    assert b$reqreads#0;
    if (*)
    {
        if (*)
        {
            assert this == this
               || (Set#Subset(Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
            assume this == this
               || _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
            assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this);
            assume read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
        }
        else
        {
            assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
               ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.ExtensibleArray.Repr];
        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.ExtensibleArray.Repr];
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)])
        {
            b$reqreads#3 := $_Frame[this, _module.ExtensibleArray.elements];
            if (read($Heap, this, _module.ExtensibleArray.elements) == null)
            {
                b$reqreads#4 := $_Frame[this, _module.ExtensibleArray.more];
            }

            if (read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null)
            {
                b$reqreads#5 := $_Frame[this, _module.ExtensibleArray.Contents];
            }

            if (!(
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box)))
            {
                b$reqreads#6 := $_Frame[this, _module.ExtensibleArray.elements];
                if (read($Heap, this, _module.ExtensibleArray.elements) != null)
                {
                    b$reqreads#7 := $_Frame[this, _module.ExtensibleArray.elements];
                    assert read($Heap, this, _module.ExtensibleArray.elements) != null;
                }

                if (read($Heap, this, _module.ExtensibleArray.elements) != null
                   && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                     == LitInt(256))
                {
                    b$reqreads#8 := $_Frame[this, _module.ExtensibleArray.elements];
                    b$reqreads#9 := $_Frame[this, _module.ExtensibleArray.Repr];
                }
            }
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))])))
        {
            b$reqreads#10 := $_Frame[this, _module.ExtensibleArray.more];
            if (read($Heap, this, _module.ExtensibleArray.more) != null)
            {
                b$reqreads#11 := $_Frame[this, _module.ExtensibleArray.more];
                b$reqreads#12 := $_Frame[this, _module.ExtensibleArray.Repr];
                if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))])
                {
                    b$reqreads#13 := $_Frame[this, _module.ExtensibleArray.more];
                    assert read($Heap, this, _module.ExtensibleArray.more) != null;
                    b$reqreads#14 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Repr];
                    b$reqreads#15 := $_Frame[this, _module.ExtensibleArray.Repr];
                }

                if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
                   && Set#Subset(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Repr), 
                    read($Heap, this, _module.ExtensibleArray.Repr)))
                {
                    b$reqreads#16 := $_Frame[this, _module.ExtensibleArray.more];
                    assert read($Heap, this, _module.ExtensibleArray.more) != null;
                    b$reqreads#17 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Repr];
                }

                if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
                   && Set#Subset(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Repr), 
                    read($Heap, this, _module.ExtensibleArray.Repr))
                   && !read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr)[$Box(this)])
                {
                    b$reqreads#18 := $_Frame[this, _module.ExtensibleArray.elements];
                    b$reqreads#19 := $_Frame[this, _module.ExtensibleArray.more];
                    assert read($Heap, this, _module.ExtensibleArray.more) != null;
                    b$reqreads#20 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Repr];
                }

                if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
                   && Set#Subset(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Repr), 
                    read($Heap, this, _module.ExtensibleArray.Repr))
                   && !read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr)[$Box(this)]
                   && !read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))])
                {
                    b$reqreads#21 := $_Frame[this, _module.ExtensibleArray.more];
                    assert read($Heap, this, _module.ExtensibleArray.more) != null;
                    b$reqreads#22 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.ExtensibleArray.more)
                             || read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.ExtensibleArray.more)))), 
                        Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.ExtensibleArray.more)))));
                    assume _module.ExtensibleArray.Valid#canCall(Tclass._System.array?(_module.ExtensibleArray$T), 
                      $Heap, 
                      read($Heap, this, _module.ExtensibleArray.more));
                }

                if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
                   && Set#Subset(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Repr), 
                    read($Heap, this, _module.ExtensibleArray.Repr))
                   && !read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr)[$Box(this)]
                   && !read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
                   && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                    $LS($LZ), 
                    $Heap, 
                    read($Heap, this, _module.ExtensibleArray.more)))
                {
                    b$reqreads#23 := $_Frame[this, _module.ExtensibleArray.more];
                    assert read($Heap, this, _module.ExtensibleArray.more) != null;
                    b$reqreads#24 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                }

                if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
                   && Set#Subset(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Repr), 
                    read($Heap, this, _module.ExtensibleArray.Repr))
                   && !read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr)[$Box(this)]
                   && !read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
                   && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                    $LS($LZ), 
                    $Heap, 
                    read($Heap, this, _module.ExtensibleArray.more))
                   && Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                     != 0)
                {
                    // Begin Comprehension WF check
                    havoc j#1;
                    if (true)
                    {
                        if (LitInt(0) <= j#1)
                        {
                            b$reqreads#25 := $_Frame[this, _module.ExtensibleArray.more];
                            assert read($Heap, this, _module.ExtensibleArray.more) != null;
                            b$reqreads#26 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                        }

                        if (LitInt(0) <= j#1
                           && j#1
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents)))
                        {
                            b$reqreads#27 := $_Frame[this, _module.ExtensibleArray.more];
                            assert read($Heap, this, _module.ExtensibleArray.more) != null;
                            b$reqreads#28 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                            assert 0 <= j#1
                               && j#1
                                 < Seq#Length(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents));
                            if ($Unbox(Seq#Index(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents), 
                                  j#1)): ref
                               != null)
                            {
                                b$reqreads#29 := $_Frame[this, _module.ExtensibleArray.more];
                                assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                b$reqreads#30 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                                assert 0 <= j#1
                                   && j#1
                                     < Seq#Length(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents));
                                assert $Unbox(Seq#Index(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents), 
                                      j#1)): ref
                                   != null;
                            }

                            if ($Unbox(Seq#Index(read($Heap, 
                                      read($Heap, this, _module.ExtensibleArray.more), 
                                      _module.ExtensibleArray.Contents), 
                                    j#1)): ref
                                 != null
                               && _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents), 
                                      j#1)): ref)
                                 == LitInt(256))
                            {
                                b$reqreads#31 := $_Frame[this, _module.ExtensibleArray.more];
                                assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                b$reqreads#32 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                                assert 0 <= j#1
                                   && j#1
                                     < Seq#Length(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents));
                                b$reqreads#33 := $_Frame[this, _module.ExtensibleArray.Repr];
                            }

                            if ($Unbox(Seq#Index(read($Heap, 
                                      read($Heap, this, _module.ExtensibleArray.more), 
                                      _module.ExtensibleArray.Contents), 
                                    j#1)): ref
                                 != null
                               && _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents), 
                                      j#1)): ref)
                                 == LitInt(256)
                               && read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#1)])
                            {
                                b$reqreads#34 := $_Frame[this, _module.ExtensibleArray.more];
                                assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                b$reqreads#35 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                                assert 0 <= j#1
                                   && j#1
                                     < Seq#Length(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents));
                                b$reqreads#36 := $_Frame[this, _module.ExtensibleArray.more];
                                assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                b$reqreads#37 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Repr];
                            }

                            if ($Unbox(Seq#Index(read($Heap, 
                                      read($Heap, this, _module.ExtensibleArray.more), 
                                      _module.ExtensibleArray.Contents), 
                                    j#1)): ref
                                 != null
                               && _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents), 
                                      j#1)): ref)
                                 == LitInt(256)
                               && read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#1)]
                               && !read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#1)])
                            {
                                b$reqreads#38 := $_Frame[this, _module.ExtensibleArray.more];
                                assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                b$reqreads#39 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                                assert 0 <= j#1
                                   && j#1
                                     < Seq#Length(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents));
                                b$reqreads#40 := $_Frame[this, _module.ExtensibleArray.elements];
                            }

                            if ($Unbox(Seq#Index(read($Heap, 
                                      read($Heap, this, _module.ExtensibleArray.more), 
                                      _module.ExtensibleArray.Contents), 
                                    j#1)): ref
                                 != null
                               && _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                        read($Heap, this, _module.ExtensibleArray.more), 
                                        _module.ExtensibleArray.Contents), 
                                      j#1)): ref)
                                 == LitInt(256)
                               && read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#1)]
                               && !read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#1)]
                               && $Unbox(Seq#Index(read($Heap, 
                                      read($Heap, this, _module.ExtensibleArray.more), 
                                      _module.ExtensibleArray.Contents), 
                                    j#1)): ref
                                 != read($Heap, this, _module.ExtensibleArray.elements))
                            {
                                // Begin Comprehension WF check
                                havoc k#1;
                                if (true)
                                {
                                    if (LitInt(0) <= k#1)
                                    {
                                        b$reqreads#41 := $_Frame[this, _module.ExtensibleArray.more];
                                        assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                        b$reqreads#42 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                                    }

                                    if (LitInt(0) <= k#1
                                       && k#1
                                         < Seq#Length(read($Heap, 
                                            read($Heap, this, _module.ExtensibleArray.more), 
                                            _module.ExtensibleArray.Contents)))
                                    {
                                    }

                                    if (LitInt(0) <= k#1
                                       && k#1
                                         < Seq#Length(read($Heap, 
                                            read($Heap, this, _module.ExtensibleArray.more), 
                                            _module.ExtensibleArray.Contents))
                                       && k#1 != j#1)
                                    {
                                        b$reqreads#43 := $_Frame[this, _module.ExtensibleArray.more];
                                        assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                        b$reqreads#44 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                                        assert 0 <= j#1
                                           && j#1
                                             < Seq#Length(read($Heap, 
                                                read($Heap, this, _module.ExtensibleArray.more), 
                                                _module.ExtensibleArray.Contents));
                                        b$reqreads#45 := $_Frame[this, _module.ExtensibleArray.more];
                                        assert read($Heap, this, _module.ExtensibleArray.more) != null;
                                        b$reqreads#46 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                                        assert 0 <= k#1
                                           && k#1
                                             < Seq#Length(read($Heap, 
                                                read($Heap, this, _module.ExtensibleArray.more), 
                                                _module.ExtensibleArray.Contents));
                                    }
                                }

                                // End Comprehension WF check
                            }
                        }
                    }

                    // End Comprehension WF check
                }
            }
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
               && Set#Subset(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr), 
                read($Heap, this, _module.ExtensibleArray.Repr))
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(this)]
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
               && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                $LS($LZ), 
                $Heap, 
                read($Heap, this, _module.ExtensibleArray.more))
               && Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))
                 != 0
               && (forall j#2: int :: 
                { $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref } 
                true
                   ==> (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != null)
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref)
                         == LitInt(256))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> !read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != read($Heap, this, _module.ExtensibleArray.elements))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> (forall k#2: int :: 
                        { $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#2)): ref } 
                        true
                           ==> 
                          LitInt(0) <= k#2
                             && k#2
                               < Seq#Length(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents))
                             && k#2 != j#2
                           ==> $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#2)): ref
                             != $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#2)): ref)))))
        {
            b$reqreads#47 := $_Frame[this, _module.ExtensibleArray.M];
            b$reqreads#48 := $_Frame[this, _module.ExtensibleArray.more];
            if (read($Heap, this, _module.ExtensibleArray.more) == null)
            {
            }
            else
            {
                b$reqreads#49 := $_Frame[this, _module.ExtensibleArray.more];
                assert read($Heap, this, _module.ExtensibleArray.more) != null;
                b$reqreads#50 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
            }
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
               && Set#Subset(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr), 
                read($Heap, this, _module.ExtensibleArray.Repr))
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(this)]
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
               && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                $LS($LZ), 
                $Heap, 
                read($Heap, this, _module.ExtensibleArray.more))
               && Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))
                 != 0
               && (forall j#2: int :: 
                { $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref } 
                true
                   ==> (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != null)
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref)
                         == LitInt(256))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> !read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != read($Heap, this, _module.ExtensibleArray.elements))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> (forall k#2: int :: 
                        { $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#2)): ref } 
                        true
                           ==> 
                          LitInt(0) <= k#2
                             && k#2
                               < Seq#Length(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents))
                             && k#2 != j#2
                           ==> $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#2)): ref
                             != $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#2)): ref))))
           && read($Heap, this, _module.ExtensibleArray.M)
             == (if read($Heap, this, _module.ExtensibleArray.more) == null
               then 0
               else Mul(LitInt(256), 
                Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents)))))
        {
            b$reqreads#51 := $_Frame[this, _module.ExtensibleArray.length];
            if (LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length))
            {
                b$reqreads#52 := $_Frame[this, _module.ExtensibleArray.length];
                b$reqreads#53 := $_Frame[this, _module.ExtensibleArray.M];
            }
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
               && Set#Subset(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr), 
                read($Heap, this, _module.ExtensibleArray.Repr))
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(this)]
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
               && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                $LS($LZ), 
                $Heap, 
                read($Heap, this, _module.ExtensibleArray.more))
               && Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))
                 != 0
               && (forall j#2: int :: 
                { $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref } 
                true
                   ==> (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != null)
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref)
                         == LitInt(256))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> !read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != read($Heap, this, _module.ExtensibleArray.elements))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> (forall k#2: int :: 
                        { $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#2)): ref } 
                        true
                           ==> 
                          LitInt(0) <= k#2
                             && k#2
                               < Seq#Length(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents))
                             && k#2 != j#2
                           ==> $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#2)): ref
                             != $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#2)): ref))))
           && read($Heap, this, _module.ExtensibleArray.M)
             == (if read($Heap, this, _module.ExtensibleArray.more) == null
               then 0
               else Mul(LitInt(256), 
                Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))))
           && 
          LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
           && read($Heap, this, _module.ExtensibleArray.length)
             <= read($Heap, this, _module.ExtensibleArray.M) + 256)
        {
            b$reqreads#54 := $_Frame[this, _module.ExtensibleArray.more];
            if (read($Heap, this, _module.ExtensibleArray.more) != null)
            {
                b$reqreads#55 := $_Frame[this, _module.ExtensibleArray.M];
                b$reqreads#56 := $_Frame[this, _module.ExtensibleArray.length];
            }
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
               && Set#Subset(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr), 
                read($Heap, this, _module.ExtensibleArray.Repr))
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(this)]
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
               && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                $LS($LZ), 
                $Heap, 
                read($Heap, this, _module.ExtensibleArray.more))
               && Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))
                 != 0
               && (forall j#2: int :: 
                { $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref } 
                true
                   ==> (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != null)
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref)
                         == LitInt(256))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> !read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != read($Heap, this, _module.ExtensibleArray.elements))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> (forall k#2: int :: 
                        { $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#2)): ref } 
                        true
                           ==> 
                          LitInt(0) <= k#2
                             && k#2
                               < Seq#Length(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents))
                             && k#2 != j#2
                           ==> $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#2)): ref
                             != $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#2)): ref))))
           && read($Heap, this, _module.ExtensibleArray.M)
             == (if read($Heap, this, _module.ExtensibleArray.more) == null
               then 0
               else Mul(LitInt(256), 
                Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))))
           && 
          LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
           && read($Heap, this, _module.ExtensibleArray.length)
             <= read($Heap, this, _module.ExtensibleArray.M) + 256
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.M)
               < read($Heap, this, _module.ExtensibleArray.length)))
        {
            b$reqreads#57 := $_Frame[this, _module.ExtensibleArray.length];
            b$reqreads#58 := $_Frame[this, _module.ExtensibleArray.Contents];
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
               && Set#Subset(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr), 
                read($Heap, this, _module.ExtensibleArray.Repr))
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(this)]
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
               && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                $LS($LZ), 
                $Heap, 
                read($Heap, this, _module.ExtensibleArray.more))
               && Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))
                 != 0
               && (forall j#2: int :: 
                { $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref } 
                true
                   ==> (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != null)
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref)
                         == LitInt(256))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> !read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != read($Heap, this, _module.ExtensibleArray.elements))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> (forall k#2: int :: 
                        { $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#2)): ref } 
                        true
                           ==> 
                          LitInt(0) <= k#2
                             && k#2
                               < Seq#Length(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents))
                             && k#2 != j#2
                           ==> $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#2)): ref
                             != $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#2)): ref))))
           && read($Heap, this, _module.ExtensibleArray.M)
             == (if read($Heap, this, _module.ExtensibleArray.more) == null
               then 0
               else Mul(LitInt(256), 
                Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))))
           && 
          LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
           && read($Heap, this, _module.ExtensibleArray.length)
             <= read($Heap, this, _module.ExtensibleArray.M) + 256
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.M)
               < read($Heap, this, _module.ExtensibleArray.length))
           && read($Heap, this, _module.ExtensibleArray.length)
             == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents)))
        {
            // Begin Comprehension WF check
            havoc i#2;
            if (true)
            {
                if (LitInt(0) <= i#2)
                {
                    b$reqreads#59 := $_Frame[this, _module.ExtensibleArray.M];
                }

                if (LitInt(0) <= i#2 && i#2 < read($Heap, this, _module.ExtensibleArray.M))
                {
                    b$reqreads#60 := $_Frame[this, _module.ExtensibleArray.Contents];
                    assert 0 <= i#2
                       && i#2 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
                    b$reqreads#61 := $_Frame[this, _module.ExtensibleArray.more];
                    assert read($Heap, this, _module.ExtensibleArray.more) != null;
                    b$reqreads#62 := $_Frame[read($Heap, this, _module.ExtensibleArray.more), _module.ExtensibleArray.Contents];
                    assert LitInt(256) != 0;
                    assert 0 <= Div(i#2, LitInt(256))
                       && Div(i#2, LitInt(256))
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents));
                    assert $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          Div(i#2, LitInt(256)))): ref
                       != null;
                    assert LitInt(256) != 0;
                    assert 0 <= Mod(i#2, LitInt(256))
                       && Mod(i#2, LitInt(256))
                         < _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              Div(i#2, LitInt(256)))): ref);
                    b$reqreads#63 := $_Frame[$Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        Div(i#2, LitInt(256)))): ref, IndexField(Mod(i#2, LitInt(256)))];
                }
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
               && Set#Subset(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr), 
                read($Heap, this, _module.ExtensibleArray.Repr))
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(this)]
               && !read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
               && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                $LS($LZ), 
                $Heap, 
                read($Heap, this, _module.ExtensibleArray.more))
               && Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))
                 != 0
               && (forall j#2: int :: 
                { $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref } 
                true
                   ==> (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != null)
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref)
                         == LitInt(256))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> !read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)])
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#2)): ref
                         != read($Heap, this, _module.ExtensibleArray.elements))
                     && (LitInt(0) <= j#2
                         && j#2
                           < Seq#Length(read($Heap, 
                              read($Heap, this, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> (forall k#2: int :: 
                        { $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#2)): ref } 
                        true
                           ==> 
                          LitInt(0) <= k#2
                             && k#2
                               < Seq#Length(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents))
                             && k#2 != j#2
                           ==> $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#2)): ref
                             != $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#2)): ref))))
           && read($Heap, this, _module.ExtensibleArray.M)
             == (if read($Heap, this, _module.ExtensibleArray.more) == null
               then 0
               else Mul(LitInt(256), 
                Seq#Length(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))))
           && 
          LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
           && read($Heap, this, _module.ExtensibleArray.length)
             <= read($Heap, this, _module.ExtensibleArray.M) + 256
           && (read($Heap, this, _module.ExtensibleArray.more) != null
             ==> read($Heap, this, _module.ExtensibleArray.M)
               < read($Heap, this, _module.ExtensibleArray.length))
           && read($Heap, this, _module.ExtensibleArray.length)
             == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
           && (forall i#4: int :: 
            { $Unbox(Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#4, 256))): ref } 
              { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4) } 
            true
               ==> 
              LitInt(0) <= i#4 && i#4 < read($Heap, this, _module.ExtensibleArray.M)
               ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4)
                 == read($Heap, 
                  $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      Div(i#4, LitInt(256)))): ref, 
                  IndexField(Mod(i#4, LitInt(256))))))
        {
            // Begin Comprehension WF check
            havoc i#3;
            if (true)
            {
                b$reqreads#64 := $_Frame[this, _module.ExtensibleArray.M];
                if (read($Heap, this, _module.ExtensibleArray.M) <= i#3)
                {
                    b$reqreads#65 := $_Frame[this, _module.ExtensibleArray.length];
                }

                if (read($Heap, this, _module.ExtensibleArray.M) <= i#3
                   && i#3 < read($Heap, this, _module.ExtensibleArray.length))
                {
                    b$reqreads#66 := $_Frame[this, _module.ExtensibleArray.Contents];
                    assert 0 <= i#3
                       && i#3 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
                    b$reqreads#67 := $_Frame[this, _module.ExtensibleArray.elements];
                    assert read($Heap, this, _module.ExtensibleArray.elements) != null;
                    b$reqreads#68 := $_Frame[this, _module.ExtensibleArray.M];
                    assert 0 <= i#3 - read($Heap, this, _module.ExtensibleArray.M)
                       && i#3 - read($Heap, this, _module.ExtensibleArray.M)
                         < _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements));
                    b$reqreads#69 := $_Frame[read($Heap, this, _module.ExtensibleArray.elements), IndexField(i#3 - read($Heap, this, _module.ExtensibleArray.M))];
                }
            }

            // End Comprehension WF check
        }

        assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
           == (
            read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
             && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
             && ((
                read($Heap, this, _module.ExtensibleArray.elements) == null
                 && read($Heap, this, _module.ExtensibleArray.more) == null
                 && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
               || (
                read($Heap, this, _module.ExtensibleArray.elements) != null
                 && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                   == LitInt(256)
                 && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
             && (read($Heap, this, _module.ExtensibleArray.more) != null
               ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
                 && Set#Subset(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Repr), 
                  read($Heap, this, _module.ExtensibleArray.Repr))
                 && !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[$Box(this)]
                 && !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
                 && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
                  $LS($LZ), 
                  $Heap, 
                  read($Heap, this, _module.ExtensibleArray.more))
                 && Seq#Length(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Contents))
                   != 0
                 && (forall j#2: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)): ref } 
                  true
                     ==> (LitInt(0) <= j#2
                           && j#2
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref
                           != null)
                       && (LitInt(0) <= j#2
                           && j#2
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#2)): ref)
                           == LitInt(256))
                       && (LitInt(0) <= j#2
                           && j#2
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#2)])
                       && (LitInt(0) <= j#2
                           && j#2
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> !read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#2)])
                       && (LitInt(0) <= j#2
                           && j#2
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> $Unbox(Seq#Index(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#2)): ref
                           != read($Heap, this, _module.ExtensibleArray.elements))
                       && (LitInt(0) <= j#2
                           && j#2
                             < Seq#Length(read($Heap, 
                                read($Heap, this, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                         ==> (forall k#2: int :: 
                          { $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, this, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#2)): ref } 
                          true
                             ==> 
                            LitInt(0) <= k#2
                               && k#2
                                 < Seq#Length(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents))
                               && k#2 != j#2
                             ==> $Unbox(Seq#Index(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents), 
                                  j#2)): ref
                               != $Unbox(Seq#Index(read($Heap, 
                                    read($Heap, this, _module.ExtensibleArray.more), 
                                    _module.ExtensibleArray.Contents), 
                                  k#2)): ref))))
             && read($Heap, this, _module.ExtensibleArray.M)
               == (if read($Heap, this, _module.ExtensibleArray.more) == null
                 then 0
                 else Mul(LitInt(256), 
                  Seq#Length(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Contents))))
             && 
            LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
             && read($Heap, this, _module.ExtensibleArray.length)
               <= read($Heap, this, _module.ExtensibleArray.M) + 256
             && (read($Heap, this, _module.ExtensibleArray.more) != null
               ==> read($Heap, this, _module.ExtensibleArray.M)
                 < read($Heap, this, _module.ExtensibleArray.length))
             && read($Heap, this, _module.ExtensibleArray.length)
               == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
             && (forall i#4: int :: 
              { $Unbox(Seq#Index(read($Heap, 
                      read($Heap, this, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Contents), 
                    Div(i#4, 256))): ref } 
                { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4) } 
              true
                 ==> 
                LitInt(0) <= i#4 && i#4 < read($Heap, this, _module.ExtensibleArray.M)
                 ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4)
                   == read($Heap, 
                    $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        Div(i#4, LitInt(256)))): ref, 
                    IndexField(Mod(i#4, LitInt(256)))))
             && (forall i#5: int :: 
              { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#5) } 
              true
                 ==> 
                read($Heap, this, _module.ExtensibleArray.M) <= i#5
                   && i#5 < read($Heap, this, _module.ExtensibleArray.length)
                 ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#5)
                   == read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.elements), 
                    IndexField(i#5 - read($Heap, this, _module.ExtensibleArray.M)))));
        assume read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
           ==> 
          !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
           ==> 
          (
              read($Heap, this, _module.ExtensibleArray.elements) == null
               && read($Heap, this, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, this, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))])
           ==> 
          read($Heap, this, _module.ExtensibleArray.more) != null
           ==> 
          read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
           ==> 
          Set#Subset(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Repr), 
            read($Heap, this, _module.ExtensibleArray.Repr))
           ==> 
          !read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr)[$Box(this)]
           ==> 
          !read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
           ==> _module.ExtensibleArray.Valid#canCall(Tclass._System.array?(_module.ExtensibleArray$T), 
            $Heap, 
            read($Heap, this, _module.ExtensibleArray.more));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this), 
          TBool);
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
        assert b$reqreads#56;
        assert b$reqreads#57;
        assert b$reqreads#58;
        assert b$reqreads#59;
        assert b$reqreads#60;
        assert b$reqreads#61;
        assert b$reqreads#62;
        assert b$reqreads#63;
        assert b$reqreads#64;
        assert b$reqreads#65;
        assert b$reqreads#66;
        assert b$reqreads#67;
        assert b$reqreads#68;
        assert b$reqreads#69;
    }
}



procedure CheckWellformed$$_module.ExtensibleArray.Init(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.ExtensibleArray.Init(_module.ExtensibleArray$T: Ty)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     && 
    _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
     && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
     && ((
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
         && Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr))
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
         && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LZ), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more))
         && Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0
         && (forall j#0: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#0)): ref } 
          true
             ==> (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != null)
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#0)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#0: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#0)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#0
                       && k#0
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#0 != j#0
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#0)): ref))))
     && read($Heap, this, _module.ExtensibleArray.M)
       == (if read($Heap, this, _module.ExtensibleArray.more) == null
         then 0
         else Mul(LitInt(256), 
          Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))))
     && 
    LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
     && read($Heap, this, _module.ExtensibleArray.length)
       <= read($Heap, this, _module.ExtensibleArray.M) + 256
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.M)
         < read($Heap, this, _module.ExtensibleArray.length))
     && read($Heap, this, _module.ExtensibleArray.length)
       == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
     && (forall i#0: int :: 
      { $Unbox(Seq#Index(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents), 
            Div(i#0, 256))): ref } 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0) } 
      true
         ==> 
        LitInt(0) <= i#0 && i#0 < read($Heap, this, _module.ExtensibleArray.M)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0)
           == read($Heap, 
            $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                Div(i#0, LitInt(256)))): ref, 
            IndexField(Mod(i#0, LitInt(256)))))
     && (forall i#1: int :: 
      { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1) } 
      true
         ==> 
        read($Heap, this, _module.ExtensibleArray.M) <= i#1
           && i#1 < read($Heap, this, _module.ExtensibleArray.length)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1)
           == read($Heap, 
            read($Heap, this, _module.ExtensibleArray.elements), 
            IndexField(i#1 - read($Heap, this, _module.ExtensibleArray.M))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)] } 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box);
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ExtensibleArray.Init(_module.ExtensibleArray$T: Ty)
   returns (this: ref
       where this != null
         && $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T)), 
    $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)];
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || 
      (
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr)));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more)));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> (forall j#1: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#1)): ref } 
          true
             ==> (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != null)
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#1)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#1: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#1)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#1
                       && k#1
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#1 != j#1
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#1)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#1)): ref))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.M)
         == (if read($Heap, this, _module.ExtensibleArray.more) == null
           then 0
           else Mul(LitInt(256), 
            Seq#Length(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         <= read($Heap, this, _module.ExtensibleArray.M) + 256;
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.M)
           < read($Heap, this, _module.ExtensibleArray.length));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#2: int :: 
        { $Unbox(Seq#Index(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents), 
              Div(i#2, 256))): ref } 
          { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2) } 
        true
           ==> 
          LitInt(0) <= i#2 && i#2 < read($Heap, this, _module.ExtensibleArray.M)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2)
             == read($Heap, 
              $Unbox(Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#2, LitInt(256)))): ref, 
              IndexField(Mod(i#2, LitInt(256)))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#3: int :: 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3) } 
        true
           ==> 
          read($Heap, this, _module.ExtensibleArray.M) <= i#3
             && i#3 < read($Heap, this, _module.ExtensibleArray.length)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3)
             == read($Heap, 
              read($Heap, this, _module.ExtensibleArray.elements), 
              IndexField(i#3 - read($Heap, this, _module.ExtensibleArray.M))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)] } 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ExtensibleArray.Init(_module.ExtensibleArray$T: Ty) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Contents: Seq Box;
  var this.Repr: Set Box;
  var this.elements: ref;
  var this.more: ref;
  var this.length: int;
  var this.M: int;

    // AddMethodImpl: Init, Impl$$_module.ExtensibleArray.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(45,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(45,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(46,14)
    assume true;
    assume true;
    this.elements := null;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(46,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(47,10)
    assume true;
    assume true;
    this.more := null;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(47,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(48,12)
    assume true;
    assume true;
    this.length := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(48,15)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(49,7)
    assume true;
    assume true;
    this.M := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(49,10)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(51,14)
    assume true;
    assume true;
    this.Contents := Lit(Seq#Empty(): Seq Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(51,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(52,10)
    assume true;
    assume true;
    assert $Is(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), TSet(Tclass._System.object?()));
    this.Repr := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(52,18)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(45,3)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.ExtensibleArray.Contents) == this.Contents;
    assume read($Heap, this, _module.ExtensibleArray.Repr) == this.Repr;
    assume read($Heap, this, _module.ExtensibleArray.elements) == this.elements;
    assume read($Heap, this, _module.ExtensibleArray.more) == this.more;
    assume read($Heap, this, _module.ExtensibleArray.length) == this.length;
    assume read($Heap, this, _module.ExtensibleArray.M) == this.M;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(45,3)
}



procedure CheckWellformed$$_module.ExtensibleArray.Get(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    i#0: int)
   returns (t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ExtensibleArray.Get(_module.ExtensibleArray$T: Ty, this: ref, i#0: int) returns (t#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Get, CheckWellformed$$_module.ExtensibleArray.Get
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(55,9): initial state"} true;
    assume _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
    assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this);
    if (LitInt(0) <= i#0)
    {
    }

    assume LitInt(0) <= i#0
       && i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc t#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(58,14): post-state"} true;
    assert 0 <= i#0
       && i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
    assume t#0 == Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0);
}



procedure Call$$_module.ExtensibleArray.Get(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    i#0: int)
   returns (t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap));
  // user-defined preconditions
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)];
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || 
      (
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr)));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more)));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> (forall j#0: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#0)): ref } 
          true
             ==> (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != null)
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#0)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#0: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#0)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#0
                       && k#0
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#0 != j#0
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#0)): ref))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.M)
         == (if read($Heap, this, _module.ExtensibleArray.more) == null
           then 0
           else Mul(LitInt(256), 
            Seq#Length(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         <= read($Heap, this, _module.ExtensibleArray.M) + 256;
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.M)
           < read($Heap, this, _module.ExtensibleArray.length));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#1: int :: 
        { $Unbox(Seq#Index(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents), 
              Div(i#1, 256))): ref } 
          { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1) } 
        true
           ==> 
          LitInt(0) <= i#1 && i#1 < read($Heap, this, _module.ExtensibleArray.M)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1)
             == read($Heap, 
              $Unbox(Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#1, LitInt(256)))): ref, 
              IndexField(Mod(i#1, LitInt(256)))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#2: int :: 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2) } 
        true
           ==> 
          read($Heap, this, _module.ExtensibleArray.M) <= i#2
             && i#2 < read($Heap, this, _module.ExtensibleArray.length)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2)
             == read($Heap, 
              read($Heap, this, _module.ExtensibleArray.elements), 
              IndexField(i#2 - read($Heap, this, _module.ExtensibleArray.M))));
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures t#0 == Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ExtensibleArray.Get(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    i#0: int)
   returns (defass#t#0: bool, 
    t#0: Box
       where defass#t#0
         ==> $IsBox(t#0, _module.ExtensibleArray$T)
           && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap), 
    $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     && 
    _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
     && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
     && ((
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
         && Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr))
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
         && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LZ), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more))
         && Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0
         && (forall j#1: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#1)): ref } 
          true
             ==> (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != null)
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#1)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#1: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#1)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#1
                       && k#1
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#1 != j#1
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#1)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#1)): ref))))
     && read($Heap, this, _module.ExtensibleArray.M)
       == (if read($Heap, this, _module.ExtensibleArray.more) == null
         then 0
         else Mul(LitInt(256), 
          Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))))
     && 
    LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
     && read($Heap, this, _module.ExtensibleArray.length)
       <= read($Heap, this, _module.ExtensibleArray.M) + 256
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.M)
         < read($Heap, this, _module.ExtensibleArray.length))
     && read($Heap, this, _module.ExtensibleArray.length)
       == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
     && (forall i#3: int :: 
      { $Unbox(Seq#Index(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents), 
            Div(i#3, 256))): ref } 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3) } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < read($Heap, this, _module.ExtensibleArray.M)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3)
           == read($Heap, 
            $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                Div(i#3, LitInt(256)))): ref, 
            IndexField(Mod(i#3, LitInt(256)))))
     && (forall i#4: int :: 
      { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4) } 
      true
         ==> 
        read($Heap, this, _module.ExtensibleArray.M) <= i#4
           && i#4 < read($Heap, this, _module.ExtensibleArray.length)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4)
           == read($Heap, 
            read($Heap, this, _module.ExtensibleArray.elements), 
            IndexField(i#4 - read($Heap, this, _module.ExtensibleArray.M))));
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures t#0 == Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ExtensibleArray.Get(_module.ExtensibleArray$T: Ty, this: ref, i#0: int)
   returns (defass#t#0: bool, t#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var arr#0: ref
     where $Is(arr#0, Tclass._System.array?(_module.ExtensibleArray$T))
       && $IsAlloc(arr#0, Tclass._System.array?(_module.ExtensibleArray$T), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._System.array?(_module.ExtensibleArray$T))
       && $IsAlloc($rhs##0, Tclass._System.array?(_module.ExtensibleArray$T), $Heap);
  var i##0: int;
  var $tmp##0: Box;

    // AddMethodImpl: Get, Impl$$_module.ExtensibleArray.Get
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(60,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(61,5)
    assume true;
    if (read($Heap, this, _module.ExtensibleArray.M) <= i#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(62,9)
        assume true;
        assert read($Heap, this, _module.ExtensibleArray.elements) != null;
        assert 0 <= i#0 - read($Heap, this, _module.ExtensibleArray.M)
           && i#0 - read($Heap, this, _module.ExtensibleArray.M)
             < _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements));
        assume true;
        t#0 := read($Heap, 
          read($Heap, this, _module.ExtensibleArray.elements), 
          IndexField(i#0 - read($Heap, this, _module.ExtensibleArray.M)));
        defass#t#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(62,26)"} true;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(64,26)
        assume true;
        // TrCallStmt: Adding lhs with type array?<T>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert read($Heap, this, _module.ExtensibleArray.more) != null;
        assert LitInt(256) != 0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        i##0 := Div(i#0, LitInt(256));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert Set#Subset(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Repr), 
            read(old($Heap), this, _module.ExtensibleArray.Repr))
           && !Set#Subset(read(old($Heap), this, _module.ExtensibleArray.Repr), 
            read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Repr));
        // ProcessCallStmt: Make the call
        call $tmp##0 := Call$$_module.ExtensibleArray.Get(Tclass._System.array?(_module.ExtensibleArray$T), read($Heap, this, _module.ExtensibleArray.more), i##0);
        havoc $rhs##0;
        assume $rhs##0 == $Unbox($tmp##0): ref;
        // TrCallStmt: After ProcessCallStmt
        arr#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(64,34)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(65,9)
        assume true;
        assert arr#0 != null;
        assert LitInt(256) != 0;
        assert 0 <= Mod(i#0, LitInt(256))
           && Mod(i#0, LitInt(256)) < _System.array.Length(arr#0);
        assume true;
        t#0 := read($Heap, arr#0, IndexField(Mod(i#0, LitInt(256))));
        defass#t#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(65,23)"} true;
    }

    assert defass#t#0;
}



procedure CheckWellformed$$_module.ExtensibleArray.Set(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    i#0: int, 
    t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ExtensibleArray.Set(_module.ExtensibleArray$T: Ty, this: ref, i#0: int, t#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Set, CheckWellformed$$_module.ExtensibleArray.Set
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(69,9): initial state"} true;
    assume _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
    assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this);
    if (LitInt(0) <= i#0)
    {
    }

    assume LitInt(0) <= i#0
       && i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(73,20): post-state"} true;
    assume _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
    assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this);
    assert $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), old($Heap));
    assert 0 <= i#0
       && i#0 < Seq#Length(read(old($Heap), this, _module.ExtensibleArray.Contents));
    assume Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), 
      Seq#Update(read(old($Heap), this, _module.ExtensibleArray.Contents), i#0, t#0));
}



procedure Call$$_module.ExtensibleArray.Set(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    i#0: int, 
    t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap));
  // user-defined preconditions
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)];
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || 
      (
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr)));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more)));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> (forall j#0: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#0)): ref } 
          true
             ==> (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != null)
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#0)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#0: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#0)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#0
                       && k#0
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#0 != j#0
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#0)): ref))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.M)
         == (if read($Heap, this, _module.ExtensibleArray.more) == null
           then 0
           else Mul(LitInt(256), 
            Seq#Length(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         <= read($Heap, this, _module.ExtensibleArray.M) + 256;
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.M)
           < read($Heap, this, _module.ExtensibleArray.length));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#1: int :: 
        { $Unbox(Seq#Index(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents), 
              Div(i#1, 256))): ref } 
          { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1) } 
        true
           ==> 
          LitInt(0) <= i#1 && i#1 < read($Heap, this, _module.ExtensibleArray.M)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1)
             == read($Heap, 
              $Unbox(Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#1, LitInt(256)))): ref, 
              IndexField(Mod(i#1, LitInt(256)))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#2: int :: 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2) } 
        true
           ==> 
          read($Heap, this, _module.ExtensibleArray.M) <= i#2
             && i#2 < read($Heap, this, _module.ExtensibleArray.length)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2)
             == read($Heap, 
              read($Heap, this, _module.ExtensibleArray.elements), 
              IndexField(i#2 - read($Heap, this, _module.ExtensibleArray.M))));
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     && 
    _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
     && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
     && ((
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
         && Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr))
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
         && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LZ), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more))
         && Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0
         && (forall j#1: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#1)): ref } 
          true
             ==> (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != null)
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#1)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#1: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#1)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#1
                       && k#1
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#1 != j#1
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#1)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#1)): ref))))
     && read($Heap, this, _module.ExtensibleArray.M)
       == (if read($Heap, this, _module.ExtensibleArray.more) == null
         then 0
         else Mul(LitInt(256), 
          Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))))
     && 
    LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
     && read($Heap, this, _module.ExtensibleArray.length)
       <= read($Heap, this, _module.ExtensibleArray.M) + 256
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.M)
         < read($Heap, this, _module.ExtensibleArray.length))
     && read($Heap, this, _module.ExtensibleArray.length)
       == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
     && (forall i#3: int :: 
      { $Unbox(Seq#Index(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents), 
            Div(i#3, 256))): ref } 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3) } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < read($Heap, this, _module.ExtensibleArray.M)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3)
           == read($Heap, 
            $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                Div(i#3, LitInt(256)))): ref, 
            IndexField(Mod(i#3, LitInt(256)))))
     && (forall i#4: int :: 
      { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4) } 
      true
         ==> 
        read($Heap, this, _module.ExtensibleArray.M) <= i#4
           && i#4 < read($Heap, this, _module.ExtensibleArray.length)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4)
           == read($Heap, 
            read($Heap, this, _module.ExtensibleArray.elements), 
            IndexField(i#4 - read($Heap, this, _module.ExtensibleArray.M))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), 
    Seq#Update(read(old($Heap), this, _module.ExtensibleArray.Contents), i#0, t#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ExtensibleArray.Set(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    i#0: int, 
    t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     && 
    _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
     && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
     && ((
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
         && Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr))
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
         && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LZ), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more))
         && Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0
         && (forall j#2: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#2)): ref } 
          true
             ==> (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref
                   != null)
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#2)])
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#2)])
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#2: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#2)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#2
                       && k#2
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#2 != j#2
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#2)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#2)): ref))))
     && read($Heap, this, _module.ExtensibleArray.M)
       == (if read($Heap, this, _module.ExtensibleArray.more) == null
         then 0
         else Mul(LitInt(256), 
          Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))))
     && 
    LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
     && read($Heap, this, _module.ExtensibleArray.length)
       <= read($Heap, this, _module.ExtensibleArray.M) + 256
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.M)
         < read($Heap, this, _module.ExtensibleArray.length))
     && read($Heap, this, _module.ExtensibleArray.length)
       == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
     && (forall i#5: int :: 
      { $Unbox(Seq#Index(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents), 
            Div(i#5, 256))): ref } 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#5) } 
      true
         ==> 
        LitInt(0) <= i#5 && i#5 < read($Heap, this, _module.ExtensibleArray.M)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#5)
           == read($Heap, 
            $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                Div(i#5, LitInt(256)))): ref, 
            IndexField(Mod(i#5, LitInt(256)))))
     && (forall i#6: int :: 
      { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#6) } 
      true
         ==> 
        read($Heap, this, _module.ExtensibleArray.M) <= i#6
           && i#6 < read($Heap, this, _module.ExtensibleArray.length)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#6)
           == read($Heap, 
            read($Heap, this, _module.ExtensibleArray.elements), 
            IndexField(i#6 - read($Heap, this, _module.ExtensibleArray.M))));
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)];
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || 
      (
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr)));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more)));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> (forall j#3: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#3)): ref } 
          true
             ==> (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#3)): ref
                   != null)
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#3)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#3)])
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#3)])
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#3)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#3: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#3)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#3
                       && k#3
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#3 != j#3
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#3)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#3)): ref))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.M)
         == (if read($Heap, this, _module.ExtensibleArray.more) == null
           then 0
           else Mul(LitInt(256), 
            Seq#Length(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         <= read($Heap, this, _module.ExtensibleArray.M) + 256;
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.M)
           < read($Heap, this, _module.ExtensibleArray.length));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#7: int :: 
        { $Unbox(Seq#Index(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents), 
              Div(i#7, 256))): ref } 
          { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#7) } 
        true
           ==> 
          LitInt(0) <= i#7 && i#7 < read($Heap, this, _module.ExtensibleArray.M)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#7)
             == read($Heap, 
              $Unbox(Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#7, LitInt(256)))): ref, 
              IndexField(Mod(i#7, LitInt(256)))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#8: int :: 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#8) } 
        true
           ==> 
          read($Heap, this, _module.ExtensibleArray.M) <= i#8
             && i#8 < read($Heap, this, _module.ExtensibleArray.length)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#8)
             == read($Heap, 
              read($Heap, this, _module.ExtensibleArray.elements), 
              IndexField(i#8 - read($Heap, this, _module.ExtensibleArray.M))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), 
    Seq#Update(read(old($Heap), this, _module.ExtensibleArray.Contents), i#0, t#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ExtensibleArray.Set(_module.ExtensibleArray$T: Ty, this: ref, i#0: int, t#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: Box where $IsBox($rhs#0_0, _module.ExtensibleArray$T);
  var arr#0: ref
     where $Is(arr#0, Tclass._System.array?(_module.ExtensibleArray$T))
       && $IsAlloc(arr#0, Tclass._System.array?(_module.ExtensibleArray$T), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._System.array?(_module.ExtensibleArray$T))
       && $IsAlloc($rhs##0, Tclass._System.array?(_module.ExtensibleArray$T), $Heap);
  var i##0: int;
  var $tmp##0: Box;
  var $rhs#0: Box where $IsBox($rhs#0, _module.ExtensibleArray$T);
  var $rhs#1: Seq Box where $Is($rhs#1, TSeq(_module.ExtensibleArray$T));

    // AddMethodImpl: Set, Impl$$_module.ExtensibleArray.Set
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(75,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(76,5)
    assume true;
    if (read($Heap, this, _module.ExtensibleArray.M) <= i#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(77,23)
        assert read($Heap, this, _module.ExtensibleArray.elements) != null;
        assert 0 <= i#0 - read($Heap, this, _module.ExtensibleArray.M)
           && i#0 - read($Heap, this, _module.ExtensibleArray.M)
             < _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements));
        assume true;
        assert $_Frame[read($Heap, this, _module.ExtensibleArray.elements), IndexField(i#0 - read($Heap, this, _module.ExtensibleArray.M))];
        assume true;
        $rhs#0_0 := t#0;
        $Heap := update($Heap, 
          read($Heap, this, _module.ExtensibleArray.elements), 
          IndexField(i#0 - read($Heap, this, _module.ExtensibleArray.M)), 
          $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(77,26)"} true;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(79,26)
        assume true;
        // TrCallStmt: Adding lhs with type array?<T>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert read($Heap, this, _module.ExtensibleArray.more) != null;
        assert LitInt(256) != 0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        i##0 := Div(i#0, LitInt(256));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $tmp##0 := Call$$_module.ExtensibleArray.Get(Tclass._System.array?(_module.ExtensibleArray$T), read($Heap, this, _module.ExtensibleArray.more), i##0);
        havoc $rhs##0;
        assume $rhs##0 == $Unbox($tmp##0): ref;
        // TrCallStmt: After ProcessCallStmt
        arr#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(79,34)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(80,20)
        assert arr#0 != null;
        assert LitInt(256) != 0;
        assert 0 <= Mod(i#0, LitInt(256))
           && Mod(i#0, LitInt(256)) < _System.array.Length(arr#0);
        assume true;
        assert $_Frame[arr#0, IndexField(Mod(i#0, LitInt(256)))];
        assume true;
        $rhs#0 := t#0;
        $Heap := update($Heap, arr#0, IndexField(Mod(i#0, LitInt(256))), $rhs#0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(80,23)"} true;
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(82,14)
    assume true;
    assert $_Frame[this, _module.ExtensibleArray.Contents];
    assert 0 <= i#0
       && i#0 < Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
    assume true;
    $rhs#1 := Seq#Update(read($Heap, this, _module.ExtensibleArray.Contents), i#0, t#0);
    $Heap := update($Heap, this, _module.ExtensibleArray.Contents, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(82,32)"} true;
}



procedure CheckWellformed$$_module.ExtensibleArray.Append(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ExtensibleArray.Append(_module.ExtensibleArray$T: Ty, this: ref, t#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Append, CheckWellformed$$_module.ExtensibleArray.Append
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(85,9): initial state"} true;
    assume _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
    assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(88,20): post-state"} true;
    assume _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
    assume _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this);
    assert $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), old($Heap));
    assume Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), 
      Seq#Append(read(old($Heap), this, _module.ExtensibleArray.Contents), 
        Seq#Build(Seq#Empty(): Seq Box, t#0)));
}



procedure Call$$_module.ExtensibleArray.Append(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap));
  // user-defined preconditions
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)];
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || 
      (
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr)));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more)));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> (forall j#0: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#0)): ref } 
          true
             ==> (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != null)
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#0)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#0)])
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#0
                   && j#0
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#0: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#0)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#0
                       && k#0
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#0 != j#0
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#0)): ref))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.M)
         == (if read($Heap, this, _module.ExtensibleArray.more) == null
           then 0
           else Mul(LitInt(256), 
            Seq#Length(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length);
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         <= read($Heap, this, _module.ExtensibleArray.M) + 256;
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.M)
           < read($Heap, this, _module.ExtensibleArray.length));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents), 
              Div(i#0, 256))): ref } 
          { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0) } 
        true
           ==> 
          LitInt(0) <= i#0 && i#0 < read($Heap, this, _module.ExtensibleArray.M)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#0)
             == read($Heap, 
              $Unbox(Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#0, LitInt(256)))): ref, 
              IndexField(Mod(i#0, LitInt(256)))));
  requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#1: int :: 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1) } 
        true
           ==> 
          read($Heap, this, _module.ExtensibleArray.M) <= i#1
             && i#1 < read($Heap, this, _module.ExtensibleArray.length)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#1)
             == read($Heap, 
              read($Heap, this, _module.ExtensibleArray.elements), 
              IndexField(i#1 - read($Heap, this, _module.ExtensibleArray.M))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     && 
    _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
     && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
     && ((
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
         && Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr))
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
         && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LZ), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more))
         && Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0
         && (forall j#1: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#1)): ref } 
          true
             ==> (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != null)
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#1)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#1)])
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#1)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#1
                   && j#1
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#1: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#1)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#1
                       && k#1
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#1 != j#1
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#1)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#1)): ref))))
     && read($Heap, this, _module.ExtensibleArray.M)
       == (if read($Heap, this, _module.ExtensibleArray.more) == null
         then 0
         else Mul(LitInt(256), 
          Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))))
     && 
    LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
     && read($Heap, this, _module.ExtensibleArray.length)
       <= read($Heap, this, _module.ExtensibleArray.M) + 256
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.M)
         < read($Heap, this, _module.ExtensibleArray.length))
     && read($Heap, this, _module.ExtensibleArray.length)
       == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
     && (forall i#2: int :: 
      { $Unbox(Seq#Index(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents), 
            Div(i#2, 256))): ref } 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2) } 
      true
         ==> 
        LitInt(0) <= i#2 && i#2 < read($Heap, this, _module.ExtensibleArray.M)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#2)
           == read($Heap, 
            $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                Div(i#2, LitInt(256)))): ref, 
            IndexField(Mod(i#2, LitInt(256)))))
     && (forall i#3: int :: 
      { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3) } 
      true
         ==> 
        read($Heap, this, _module.ExtensibleArray.M) <= i#3
           && i#3 < read($Heap, this, _module.ExtensibleArray.length)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#3)
           == read($Heap, 
            read($Heap, this, _module.ExtensibleArray.elements), 
            IndexField(i#3 - read($Heap, this, _module.ExtensibleArray.M))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), 
    Seq#Append(read(old($Heap), this, _module.ExtensibleArray.Contents), 
      Seq#Build(Seq#Empty(): Seq Box, t#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ExtensibleArray.Append(_module.ExtensibleArray$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
         && $IsAlloc(this, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module.ExtensibleArray$T)
         && $IsAllocBox(t#0, _module.ExtensibleArray$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     && 
    _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)]
     && !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)]
     && ((
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]))
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]
         && Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr))
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]
         && !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]
         && _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LZ), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more))
         && Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0
         && (forall j#2: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#2)): ref } 
          true
             ==> (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref
                   != null)
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#2)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#2)])
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#2)])
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#2)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#2
                   && j#2
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#2: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#2)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#2
                       && k#2
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#2 != j#2
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#2)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#2)): ref))))
     && read($Heap, this, _module.ExtensibleArray.M)
       == (if read($Heap, this, _module.ExtensibleArray.more) == null
         then 0
         else Mul(LitInt(256), 
          Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))))
     && 
    LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length)
     && read($Heap, this, _module.ExtensibleArray.length)
       <= read($Heap, this, _module.ExtensibleArray.M) + 256
     && (read($Heap, this, _module.ExtensibleArray.more) != null
       ==> read($Heap, this, _module.ExtensibleArray.M)
         < read($Heap, this, _module.ExtensibleArray.length))
     && read($Heap, this, _module.ExtensibleArray.length)
       == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents))
     && (forall i#4: int :: 
      { $Unbox(Seq#Index(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents), 
            Div(i#4, 256))): ref } 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4) } 
      true
         ==> 
        LitInt(0) <= i#4 && i#4 < read($Heap, this, _module.ExtensibleArray.M)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#4)
           == read($Heap, 
            $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                Div(i#4, LitInt(256)))): ref, 
            IndexField(Mod(i#4, LitInt(256)))))
     && (forall i#5: int :: 
      { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#5) } 
      true
         ==> 
        read($Heap, this, _module.ExtensibleArray.M) <= i#5
           && i#5 < read($Heap, this, _module.ExtensibleArray.length)
         ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#5)
           == read($Heap, 
            read($Heap, this, _module.ExtensibleArray.elements), 
            IndexField(i#5 - read($Heap, this, _module.ExtensibleArray.M))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.Repr)[$Box(this)];
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || !read($Heap, this, _module.ExtensibleArray.Repr)[$Box(null)];
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || 
      (
        read($Heap, this, _module.ExtensibleArray.elements) == null
         && read($Heap, this, _module.ExtensibleArray.more) == null
         && Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
       || (
        read($Heap, this, _module.ExtensibleArray.elements) != null
         && _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements))
           == LitInt(256)
         && read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.more))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Set#Subset(read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr), 
          read($Heap, this, _module.ExtensibleArray.Repr)));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(this)]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> !read($Heap, 
          read($Heap, this, _module.ExtensibleArray.more), 
          _module.ExtensibleArray.Repr)[$Box(read($Heap, this, _module.ExtensibleArray.elements))]);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> _module.ExtensibleArray.Valid(Tclass._System.array?(_module.ExtensibleArray$T), 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, this, _module.ExtensibleArray.more)));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           != 0);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> (forall j#3: int :: 
          { $Unbox(Seq#Index(read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents), 
                j#3)): ref } 
          true
             ==> (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#3)): ref
                   != null)
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#3)): ref)
                   == LitInt(256))
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> read($Heap, this, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#3)])
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> !read($Heap, 
                  read($Heap, this, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  j#3)])
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> $Unbox(Seq#Index(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#3)): ref
                   != read($Heap, this, _module.ExtensibleArray.elements))
               && (LitInt(0) <= j#3
                   && j#3
                     < Seq#Length(read($Heap, 
                        read($Heap, this, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents))
                 ==> (forall k#3: int :: 
                  { $Unbox(Seq#Index(read($Heap, 
                          read($Heap, this, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        k#3)): ref } 
                  true
                     ==> 
                    LitInt(0) <= k#3
                       && k#3
                         < Seq#Length(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                       && k#3 != j#3
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#3)): ref
                       != $Unbox(Seq#Index(read($Heap, 
                            read($Heap, this, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          k#3)): ref))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.M)
         == (if read($Heap, this, _module.ExtensibleArray.more) == null
           then 0
           else Mul(LitInt(256), 
            Seq#Length(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.ExtensibleArray.length);
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         <= read($Heap, this, _module.ExtensibleArray.M) + 256;
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.ExtensibleArray.more) != null
         ==> read($Heap, this, _module.ExtensibleArray.M)
           < read($Heap, this, _module.ExtensibleArray.length));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.ExtensibleArray.length)
         == Seq#Length(read($Heap, this, _module.ExtensibleArray.Contents));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#6: int :: 
        { $Unbox(Seq#Index(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents), 
              Div(i#6, 256))): ref } 
          { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#6) } 
        true
           ==> 
          LitInt(0) <= i#6 && i#6 < read($Heap, this, _module.ExtensibleArray.M)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#6)
             == read($Heap, 
              $Unbox(Seq#Index(read($Heap, 
                    read($Heap, this, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#6, LitInt(256)))): ref, 
              IndexField(Mod(i#6, LitInt(256)))));
  ensures _module.ExtensibleArray.Valid#canCall(_module.ExtensibleArray$T, $Heap, this)
     ==> _module.ExtensibleArray.Valid(_module.ExtensibleArray$T, $LS($LZ), $Heap, this)
       || (forall i#7: int :: 
        { Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#7) } 
        true
           ==> 
          read($Heap, this, _module.ExtensibleArray.M) <= i#7
             && i#7 < read($Heap, this, _module.ExtensibleArray.length)
           ==> Seq#Index(read($Heap, this, _module.ExtensibleArray.Contents), i#7)
             == read($Heap, 
              read($Heap, this, _module.ExtensibleArray.elements), 
              IndexField(i#7 - read($Heap, this, _module.ExtensibleArray.M))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.ExtensibleArray.Contents), 
    Seq#Append(read(old($Heap), this, _module.ExtensibleArray.Contents), 
      Seq#Build(Seq#Empty(): Seq Box, t#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.ExtensibleArray.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ExtensibleArray.Append(_module.ExtensibleArray$T: Ty, this: ref, t#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: ref
     where $Is($rhs#0_0, Tclass._System.array?(_module.ExtensibleArray$T));
  var _v0#0_0: int;
  var $oldHeap#0_0: Heap;
  var $_Frame#l0_0: <beta>[ref,Field beta]bool;
  var lambdaResult#0_0: Box;
  var $nw: ref;
  var $rhs#0_1: Set Box where $Is($rhs#0_1, TSet(Tclass._System.object?()));
  var $rhs#1_0: Box where $IsBox($rhs#1_0, _module.ExtensibleArray$T);
  var $rhs#2_0: ref
     where $Is($rhs#2_0, 
      Tclass._module.ExtensibleArray?(Tclass._System.array?(_module.ExtensibleArray$T)));
  var $rhs#2_1: Set Box where $Is($rhs#2_1, TSet(Tclass._System.object?()));
  var t##0: ref;
  var $rhs#0: Set Box where $Is($rhs#0, TSet(Tclass._System.object?()));
  var $rhs#1: int;
  var $rhs#2: ref where $Is($rhs#2, Tclass._System.array?(_module.ExtensibleArray$T));
  var _v1#0: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: Box;
  var $rhs#3: Set Box where $Is($rhs#3, TSet(Tclass._System.object?()));
  var $rhs#4: Box where $IsBox($rhs#4, _module.ExtensibleArray$T);
  var $rhs#5: int;
  var $rhs#6: Seq Box where $Is($rhs#6, TSeq(_module.ExtensibleArray$T));

    // AddMethodImpl: Append, Impl$$_module.ExtensibleArray.Append
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.ExtensibleArray.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(91,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(92,5)
    assume true;
    if (read($Heap, this, _module.ExtensibleArray.elements) == null)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(93,16)
        assume true;
        assert $_Frame[this, _module.ExtensibleArray.elements];
        assert 0 <= LitInt(256);
        // Begin Comprehension WF check
        if (*)
        {
            havoc _v0#0_0;
            if (LitInt(0) <= _v0#0_0)
            {
                $oldHeap#0_0 := $Heap;
                havoc $Heap;
                assume $IsGoodHeap($Heap);
                assume $oldHeap#0_0 == $Heap || $HeapSucc($oldHeap#0_0, $Heap);
                $_Frame#l0_0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
                  $o != null && read($Heap, $o, alloc) ==> false);
                assume lambdaResult#0_0 == t#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $IsBox(lambdaResult#0_0, _module.ExtensibleArray$T);
            }

            assume false;
        }

        // End Comprehension WF check
        havoc $nw;
        assume $nw != null && dtype($nw) == Tclass._System.array?(_module.ExtensibleArray$T);
        assume !read($Heap, $nw, alloc);
        assume _System.array.Length($nw) == LitInt(256);
        assert {:subsumption 0} (forall arrayinit#0_0#i0#0: int :: 
          0 <= arrayinit#0_0#i0#0 && arrayinit#0_0#i0#0 < LitInt(256)
             ==> Requires1(Tclass._System.nat(), 
              _module.ExtensibleArray$T, 
              $Heap, 
              Lit(AtLayer((lambda $l#0_0#ly#0: LayerType :: 
                    Handle1((lambda $l#0_0#heap#0: Heap, $l#0_0#_v0#0: Box :: t#0), 
                      (lambda $l#0_0#heap#0: Heap, $l#0_0#_v0#0: Box :: 
                        $IsBox($l#0_0#_v0#0, Tclass._System.nat())), 
                      (lambda $l#0_0#heap#0: Heap, $l#0_0#_v0#0: Box :: 
                        SetRef_to_SetBox((lambda $l#0_0#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#0_0#i0#0)));
        assume (forall arrayinit#0_0#i0#0: int :: 
          { read($Heap, $nw, IndexField(arrayinit#0_0#i0#0)) } 
          0 <= arrayinit#0_0#i0#0 && arrayinit#0_0#i0#0 < LitInt(256)
             ==> read($Heap, $nw, IndexField(arrayinit#0_0#i0#0))
               == Apply1(Tclass._System.nat(), 
                _module.ExtensibleArray$T, 
                $Heap, 
                Lit(AtLayer((lambda $l#0_0#ly#0: LayerType :: 
                      Handle1((lambda $l#0_0#heap#0: Heap, $l#0_0#_v0#0: Box :: t#0), 
                        (lambda $l#0_0#heap#0: Heap, $l#0_0#_v0#0: Box :: 
                          $IsBox($l#0_0#_v0#0, Tclass._System.nat())), 
                        (lambda $l#0_0#heap#0: Heap, $l#0_0#_v0#0: Box :: 
                          SetRef_to_SetBox((lambda $l#0_0#o#0: ref :: false))))), 
                    $LS($LZ))), 
                $Box(arrayinit#0_0#i0#0)));
        $Heap := update($Heap, $nw, alloc, true);
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        $rhs#0_0 := $nw;
        $Heap := update($Heap, this, _module.ExtensibleArray.elements, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(93,36)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(94,12)
        assume true;
        assert $_Frame[this, _module.ExtensibleArray.Repr];
        assume true;
        $rhs#0_1 := Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.ExtensibleArray.elements))));
        $Heap := update($Heap, this, _module.ExtensibleArray.Repr, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(94,31)"} true;
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(96,5)
    if (read($Heap, this, _module.ExtensibleArray.length) != LitInt(0))
    {
        assert LitInt(256) != 0;
    }

    assume true;
    if (read($Heap, this, _module.ExtensibleArray.length) == LitInt(0)
       || Mod(read($Heap, this, _module.ExtensibleArray.length), LitInt(256)) != 0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(98,28)
        assert read($Heap, this, _module.ExtensibleArray.elements) != null;
        assert 0
             <= read($Heap, this, _module.ExtensibleArray.length)
               - read($Heap, this, _module.ExtensibleArray.M)
           && read($Heap, this, _module.ExtensibleArray.length)
               - read($Heap, this, _module.ExtensibleArray.M)
             < _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements));
        assume true;
        assert $_Frame[read($Heap, this, _module.ExtensibleArray.elements), IndexField(read($Heap, this, _module.ExtensibleArray.length)
             - read($Heap, this, _module.ExtensibleArray.M))];
        assume true;
        $rhs#1_0 := t#0;
        $Heap := update($Heap, 
          read($Heap, this, _module.ExtensibleArray.elements), 
          IndexField(read($Heap, this, _module.ExtensibleArray.length)
               - read($Heap, this, _module.ExtensibleArray.M)), 
          $rhs#1_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(98,31)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(100,7)
        assume true;
        if (read($Heap, this, _module.ExtensibleArray.more) == null)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(101,14)
            assume true;
            assert $_Frame[this, _module.ExtensibleArray.more];
            // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(101,37)
            // TrCallStmt: Before ProcessCallStmt
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $nw := Call$$_module.ExtensibleArray.Init(Tclass._System.array?(_module.ExtensibleArray$T));
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(101,42)"} true;
            $rhs#2_0 := $nw;
            $Heap := update($Heap, this, _module.ExtensibleArray.more, $rhs#2_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(101,42)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(102,14)
            assume true;
            assert $_Frame[this, _module.ExtensibleArray.Repr];
            assert read($Heap, this, _module.ExtensibleArray.more) != null;
            assume true;
            $rhs#2_1 := Set#Union(Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.ExtensibleArray.more)))), 
              read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr));
            $Heap := update($Heap, this, _module.ExtensibleArray.Repr, $rhs#2_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(102,41)"} true;
        }
        else
        {
        }

        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(105,18)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert read($Heap, this, _module.ExtensibleArray.more) != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0 := read($Heap, this, _module.ExtensibleArray.elements);
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert 0 <= Seq#Length(read(old($Heap), this, _module.ExtensibleArray.Contents))
           || Seq#Length(read($Heap, 
                read($Heap, this, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Contents))
             == Seq#Length(read(old($Heap), this, _module.ExtensibleArray.Contents));
        assert Seq#Length(read($Heap, 
              read($Heap, this, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Contents))
           < Seq#Length(read(old($Heap), this, _module.ExtensibleArray.Contents));
        // ProcessCallStmt: Make the call
        call Call$$_module.ExtensibleArray.Append(Tclass._System.array?(_module.ExtensibleArray$T), read($Heap, this, _module.ExtensibleArray.more), $Box(t##0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(105,27)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(106,12)
        assume true;
        assert $_Frame[this, _module.ExtensibleArray.Repr];
        assert read($Heap, this, _module.ExtensibleArray.more) != null;
        assume true;
        $rhs#0 := Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
          read($Heap, 
            read($Heap, this, _module.ExtensibleArray.more), 
            _module.ExtensibleArray.Repr));
        $Heap := update($Heap, this, _module.ExtensibleArray.Repr, $rhs#0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(106,30)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(107,9)
        assume true;
        assert $_Frame[this, _module.ExtensibleArray.M];
        assume true;
        $rhs#1 := read($Heap, this, _module.ExtensibleArray.M) + 256;
        $Heap := update($Heap, this, _module.ExtensibleArray.M, $rhs#1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(107,18)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(108,16)
        assume true;
        assert $_Frame[this, _module.ExtensibleArray.elements];
        assert 0 <= LitInt(256);
        // Begin Comprehension WF check
        if (*)
        {
            havoc _v1#0;
            if (LitInt(0) <= _v1#0)
            {
                $oldHeap#0 := $Heap;
                havoc $Heap;
                assume $IsGoodHeap($Heap);
                assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
                $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
                  $o != null && read($Heap, $o, alloc) ==> false);
                assume lambdaResult#0 == t#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $IsBox(lambdaResult#0, _module.ExtensibleArray$T);
            }

            assume false;
        }

        // End Comprehension WF check
        havoc $nw;
        assume $nw != null && dtype($nw) == Tclass._System.array?(_module.ExtensibleArray$T);
        assume !read($Heap, $nw, alloc);
        assume _System.array.Length($nw) == LitInt(256);
        assert {:subsumption 0} (forall arrayinit#0#i0#0: int :: 
          0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(256)
             ==> Requires1(Tclass._System.nat(), 
              _module.ExtensibleArray$T, 
              $Heap, 
              Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                    Handle1((lambda $l#0#heap#0: Heap, $l#0#_v1#0: Box :: t#0), 
                      (lambda $l#0#heap#0: Heap, $l#0#_v1#0: Box :: 
                        $IsBox($l#0#_v1#0, Tclass._System.nat())), 
                      (lambda $l#0#heap#0: Heap, $l#0#_v1#0: Box :: 
                        SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#0#i0#0)));
        assume (forall arrayinit#0#i0#0: int :: 
          { read($Heap, $nw, IndexField(arrayinit#0#i0#0)) } 
          0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(256)
             ==> read($Heap, $nw, IndexField(arrayinit#0#i0#0))
               == Apply1(Tclass._System.nat(), 
                _module.ExtensibleArray$T, 
                $Heap, 
                Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                      Handle1((lambda $l#0#heap#0: Heap, $l#0#_v1#0: Box :: t#0), 
                        (lambda $l#0#heap#0: Heap, $l#0#_v1#0: Box :: 
                          $IsBox($l#0#_v1#0, Tclass._System.nat())), 
                        (lambda $l#0#heap#0: Heap, $l#0#_v1#0: Box :: 
                          SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
                    $LS($LZ))), 
                $Box(arrayinit#0#i0#0)));
        $Heap := update($Heap, $nw, alloc, true);
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        $rhs#2 := $nw;
        $Heap := update($Heap, this, _module.ExtensibleArray.elements, $rhs#2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(108,36)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(109,12)
        assume true;
        assert $_Frame[this, _module.ExtensibleArray.Repr];
        assume true;
        $rhs#3 := Set#Union(read($Heap, this, _module.ExtensibleArray.Repr), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.ExtensibleArray.elements))));
        $Heap := update($Heap, this, _module.ExtensibleArray.Repr, $rhs#3);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(109,31)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(110,19)
        assert read($Heap, this, _module.ExtensibleArray.elements) != null;
        assert 0 <= LitInt(0)
           && LitInt(0)
             < _System.array.Length(read($Heap, this, _module.ExtensibleArray.elements));
        assume true;
        assert $_Frame[read($Heap, this, _module.ExtensibleArray.elements), IndexField(LitInt(0))];
        assume true;
        $rhs#4 := t#0;
        $Heap := update($Heap, 
          read($Heap, this, _module.ExtensibleArray.elements), 
          IndexField(LitInt(0)), 
          $rhs#4);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(110,22)"} true;
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(112,12)
    assume true;
    assert $_Frame[this, _module.ExtensibleArray.length];
    assume true;
    $rhs#5 := read($Heap, this, _module.ExtensibleArray.length) + 1;
    $Heap := update($Heap, this, _module.ExtensibleArray.length, $rhs#5);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(112,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(113,14)
    assume true;
    assert $_Frame[this, _module.ExtensibleArray.Contents];
    assume true;
    $rhs#6 := Seq#Append(read($Heap, this, _module.ExtensibleArray.Contents), 
      Seq#Build(Seq#Empty(): Seq Box, t#0));
    $Heap := update($Heap, this, _module.ExtensibleArray.Contents, $rhs#6);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(113,30)"} true;
}



// _module.ExtensibleArray: subset type $Is
axiom (forall _module.ExtensibleArray$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T)) } 
  $Is(c#0, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T))
     <==> $Is(c#0, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T))
       && c#0 != null);

// _module.ExtensibleArray: subset type $IsAlloc
axiom (forall _module.ExtensibleArray$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $h) } 
  $IsAlloc(c#0, Tclass._module.ExtensibleArray(_module.ExtensibleArray$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.ExtensibleArray?(_module.ExtensibleArray$T), $h));

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
  var a#0: ref
     where $Is(a#0, Tclass._module.ExtensibleArray(TInt))
       && $IsAlloc(a#0, Tclass._module.ExtensibleArray(TInt), $Heap);
  var $nw: ref;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var t##0_0: int;
  var k#1: int;
  var $rhs##0: int;
  var i##0: int;
  var $tmp##0: Box;
  var $rhs##1: int;
  var i##1: int;
  var $tmp##1: Box;
  var $rhs##2: int;
  var i##2: int;
  var $tmp##2: Box;
  var i##3: int;
  var t##0: int;
  var $rhs##3: int;
  var i##4: int;
  var $tmp##3: Box;
  var $rhs##4: int;
  var i##5: int;
  var $tmp##4: Box;
  var $rhs##5: int;
  var i##6: int;
  var $tmp##5: Box;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(117,14): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(118,9)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(118,32)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.ExtensibleArray.Init(TInt);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(118,37)"} true;
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(118,37)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(119,9)
    assume true;
    assume true;
    n#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(119,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(120,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Mul(LitInt(256), LitInt(256)) + 600 - n#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(a#0)];
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || !read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(null)];
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || 
          (
            read($Heap, a#0, _module.ExtensibleArray.elements) == null
             && read($Heap, a#0, _module.ExtensibleArray.more) == null
             && Seq#Equal(read($Heap, a#0, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
           || (
            read($Heap, a#0, _module.ExtensibleArray.elements) != null
             && _System.array.Length(read($Heap, a#0, _module.ExtensibleArray.elements))
               == LitInt(256)
             && read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(read($Heap, a#0, _module.ExtensibleArray.elements))]);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(read($Heap, a#0, _module.ExtensibleArray.more))]);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, a#0, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr), 
              read($Heap, a#0, _module.ExtensibleArray.Repr)));
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> !read($Heap, 
              read($Heap, a#0, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Repr)[$Box(a#0)]);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> !read($Heap, 
              read($Heap, a#0, _module.ExtensibleArray.more), 
              _module.ExtensibleArray.Repr)[$Box(read($Heap, a#0, _module.ExtensibleArray.elements))]);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> _module.ExtensibleArray.Valid(Tclass._System.array?(TInt), 
              $LS($LS($LZ)), 
              $Heap, 
              read($Heap, a#0, _module.ExtensibleArray.more)));
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> Seq#Length(read($Heap, 
                  read($Heap, a#0, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Contents))
               != 0);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> (forall j#0: int :: 
              { $Unbox(Seq#Index(read($Heap, 
                      read($Heap, a#0, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Contents), 
                    j#0)): ref } 
              true
                 ==> (LitInt(0) <= j#0
                       && j#0
                         < Seq#Length(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)): ref
                       != null)
                   && (LitInt(0) <= j#0
                       && j#0
                         < Seq#Length(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                     ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#0)): ref)
                       == LitInt(256))
                   && (LitInt(0) <= j#0
                       && j#0
                         < Seq#Length(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                     ==> read($Heap, a#0, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                        read($Heap, a#0, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)])
                   && (LitInt(0) <= j#0
                       && j#0
                         < Seq#Length(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                     ==> !read($Heap, 
                      read($Heap, a#0, _module.ExtensibleArray.more), 
                      _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                        read($Heap, a#0, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)])
                   && (LitInt(0) <= j#0
                       && j#0
                         < Seq#Length(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                     ==> $Unbox(Seq#Index(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents), 
                          j#0)): ref
                       != read($Heap, a#0, _module.ExtensibleArray.elements))
                   && (LitInt(0) <= j#0
                       && j#0
                         < Seq#Length(read($Heap, 
                            read($Heap, a#0, _module.ExtensibleArray.more), 
                            _module.ExtensibleArray.Contents))
                     ==> (forall k#0: int :: 
                      { $Unbox(Seq#Index(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            k#0)): ref } 
                      true
                         ==> 
                        LitInt(0) <= k#0
                           && k#0
                             < Seq#Length(read($Heap, 
                                read($Heap, a#0, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents))
                           && k#0 != j#0
                         ==> $Unbox(Seq#Index(read($Heap, 
                                read($Heap, a#0, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#0)): ref
                           != $Unbox(Seq#Index(read($Heap, 
                                read($Heap, a#0, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#0)): ref))));
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || read($Heap, a#0, _module.ExtensibleArray.M)
             == (if read($Heap, a#0, _module.ExtensibleArray.more) == null
               then 0
               else Mul(LitInt(256), 
                Seq#Length(read($Heap, 
                    read($Heap, a#0, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))));
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || LitInt(0) <= read($Heap, a#0, _module.ExtensibleArray.length);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || read($Heap, a#0, _module.ExtensibleArray.length)
             <= read($Heap, a#0, _module.ExtensibleArray.M) + 256;
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> read($Heap, a#0, _module.ExtensibleArray.M)
               < read($Heap, a#0, _module.ExtensibleArray.length));
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || read($Heap, a#0, _module.ExtensibleArray.length)
             == Seq#Length(read($Heap, a#0, _module.ExtensibleArray.Contents));
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (forall i#0: int :: 
            { $Unbox(Seq#Index(read($Heap, 
                    read($Heap, a#0, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#0, 256))): ref } 
              { $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#0)): int } 
            true
               ==> 
              LitInt(0) <= i#0 && i#0 < read($Heap, a#0, _module.ExtensibleArray.M)
               ==> $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#0)): int
                 == $Unbox(read($Heap, 
                    $Unbox(Seq#Index(read($Heap, 
                          read($Heap, a#0, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        Div(i#0, LitInt(256)))): ref, 
                    IndexField(Mod(i#0, LitInt(256))))): int);
      invariant $w$loop#0
         ==> 
        _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
         ==> _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           || (forall i#1: int :: 
            { $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#1)): int } 
            true
               ==> 
              read($Heap, a#0, _module.ExtensibleArray.M) <= i#1
                 && i#1 < read($Heap, a#0, _module.ExtensibleArray.length)
               ==> $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#1)): int
                 == $Unbox(read($Heap, 
                    read($Heap, a#0, _module.ExtensibleArray.elements), 
                    IndexField(i#1 - read($Heap, a#0, _module.ExtensibleArray.M)))): int);
      free invariant $w$loop#0
         ==> _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0)
           && 
          _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
           && 
          read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(a#0)]
           && !read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(null)]
           && ((
              read($Heap, a#0, _module.ExtensibleArray.elements) == null
               && read($Heap, a#0, _module.ExtensibleArray.more) == null
               && Seq#Equal(read($Heap, a#0, _module.ExtensibleArray.Contents), Seq#Empty(): Seq Box))
             || (
              read($Heap, a#0, _module.ExtensibleArray.elements) != null
               && _System.array.Length(read($Heap, a#0, _module.ExtensibleArray.elements))
                 == LitInt(256)
               && read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(read($Heap, a#0, _module.ExtensibleArray.elements))]))
           && (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box(read($Heap, a#0, _module.ExtensibleArray.more))]
               && Set#Subset(read($Heap, 
                  read($Heap, a#0, _module.ExtensibleArray.more), 
                  _module.ExtensibleArray.Repr), 
                read($Heap, a#0, _module.ExtensibleArray.Repr))
               && !read($Heap, 
                read($Heap, a#0, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(a#0)]
               && !read($Heap, 
                read($Heap, a#0, _module.ExtensibleArray.more), 
                _module.ExtensibleArray.Repr)[$Box(read($Heap, a#0, _module.ExtensibleArray.elements))]
               && _module.ExtensibleArray.Valid(Tclass._System.array?(TInt), 
                $LS($LZ), 
                $Heap, 
                read($Heap, a#0, _module.ExtensibleArray.more))
               && Seq#Length(read($Heap, 
                    read($Heap, a#0, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))
                 != 0
               && (forall j#0: int :: 
                { $Unbox(Seq#Index(read($Heap, 
                        read($Heap, a#0, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Contents), 
                      j#0)): ref } 
                true
                   ==> (LitInt(0) <= j#0
                         && j#0
                           < Seq#Length(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#0)): ref
                         != null)
                     && (LitInt(0) <= j#0
                         && j#0
                           < Seq#Length(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> _System.array.Length($Unbox(Seq#Index(read($Heap, 
                                read($Heap, a#0, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              j#0)): ref)
                         == LitInt(256))
                     && (LitInt(0) <= j#0
                         && j#0
                           < Seq#Length(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> read($Heap, a#0, _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, a#0, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#0)])
                     && (LitInt(0) <= j#0
                         && j#0
                           < Seq#Length(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> !read($Heap, 
                        read($Heap, a#0, _module.ExtensibleArray.more), 
                        _module.ExtensibleArray.Repr)[Seq#Index(read($Heap, 
                          read($Heap, a#0, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        j#0)])
                     && (LitInt(0) <= j#0
                         && j#0
                           < Seq#Length(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> $Unbox(Seq#Index(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents), 
                            j#0)): ref
                         != read($Heap, a#0, _module.ExtensibleArray.elements))
                     && (LitInt(0) <= j#0
                         && j#0
                           < Seq#Length(read($Heap, 
                              read($Heap, a#0, _module.ExtensibleArray.more), 
                              _module.ExtensibleArray.Contents))
                       ==> (forall k#0: int :: 
                        { $Unbox(Seq#Index(read($Heap, 
                                read($Heap, a#0, _module.ExtensibleArray.more), 
                                _module.ExtensibleArray.Contents), 
                              k#0)): ref } 
                        true
                           ==> 
                          LitInt(0) <= k#0
                             && k#0
                               < Seq#Length(read($Heap, 
                                  read($Heap, a#0, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents))
                             && k#0 != j#0
                           ==> $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, a#0, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                j#0)): ref
                             != $Unbox(Seq#Index(read($Heap, 
                                  read($Heap, a#0, _module.ExtensibleArray.more), 
                                  _module.ExtensibleArray.Contents), 
                                k#0)): ref))))
           && read($Heap, a#0, _module.ExtensibleArray.M)
             == (if read($Heap, a#0, _module.ExtensibleArray.more) == null
               then 0
               else Mul(LitInt(256), 
                Seq#Length(read($Heap, 
                    read($Heap, a#0, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents))))
           && 
          LitInt(0) <= read($Heap, a#0, _module.ExtensibleArray.length)
           && read($Heap, a#0, _module.ExtensibleArray.length)
             <= read($Heap, a#0, _module.ExtensibleArray.M) + 256
           && (read($Heap, a#0, _module.ExtensibleArray.more) != null
             ==> read($Heap, a#0, _module.ExtensibleArray.M)
               < read($Heap, a#0, _module.ExtensibleArray.length))
           && read($Heap, a#0, _module.ExtensibleArray.length)
             == Seq#Length(read($Heap, a#0, _module.ExtensibleArray.Contents))
           && (forall i#0: int :: 
            { $Unbox(Seq#Index(read($Heap, 
                    read($Heap, a#0, _module.ExtensibleArray.more), 
                    _module.ExtensibleArray.Contents), 
                  Div(i#0, 256))): ref } 
              { $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#0)): int } 
            true
               ==> 
              LitInt(0) <= i#0 && i#0 < read($Heap, a#0, _module.ExtensibleArray.M)
               ==> $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#0)): int
                 == $Unbox(read($Heap, 
                    $Unbox(Seq#Index(read($Heap, 
                          read($Heap, a#0, _module.ExtensibleArray.more), 
                          _module.ExtensibleArray.Contents), 
                        Div(i#0, LitInt(256)))): ref, 
                    IndexField(Mod(i#0, LitInt(256))))): int)
           && (forall i#1: int :: 
            { $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#1)): int } 
            true
               ==> 
              read($Heap, a#0, _module.ExtensibleArray.M) <= i#1
                 && i#1 < read($Heap, a#0, _module.ExtensibleArray.length)
               ==> $Unbox(Seq#Index(read($Heap, a#0, _module.ExtensibleArray.Contents), i#1)): int
                 == $Unbox(read($Heap, 
                    read($Heap, a#0, _module.ExtensibleArray.elements), 
                    IndexField(i#1 - read($Heap, a#0, _module.ExtensibleArray.M)))): int);
      invariant $w$loop#0
         ==> (forall $o: ref :: 
          { read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box($o)] } 
          read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> Seq#Length(read($Heap, a#0, _module.ExtensibleArray.Contents)) == n#0;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Mul(LitInt(256), LitInt(256)) + 600 - n#0 <= $decr_init$loop#00
         && (Mul(LitInt(256), LitInt(256)) + 600 - n#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(120,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert {:subsumption 0} a#0 != null;
            assume _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0);
            if (_module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0))
            {
                assert {:subsumption 0} a#0 != null;
            }

            assume _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0);
            assume _module.ExtensibleArray.Valid(TInt, $LS($LZ), $Heap, a#0)
               && (forall $o: ref :: 
                { read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box($o)] } 
                read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc));
            assert {:subsumption 0} a#0 != null;
            assume true;
            assume Seq#Length(read($Heap, a#0, _module.ExtensibleArray.Contents)) == n#0;
            assume true;
            assume false;
        }

        assume true;
        if (Mul(LitInt(256), LitInt(256)) + 600 <= n#0)
        {
            break;
        }

        $decr$loop#00 := Mul(LitInt(256), LitInt(256)) + 600 - n#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(124,13)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert a#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0_0 := n#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.ExtensibleArray.Append(TInt, a#0, $Box(t##0_0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(124,15)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(125,7)
        assume true;
        assume true;
        n#0 := n#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(125,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(120,3)
        assert 0 <= $decr$loop#00 || Mul(LitInt(256), LitInt(256)) + 600 - n#0 == $decr$loop#00;
        assert Mul(LitInt(256), LitInt(256)) + 600 - n#0 < $decr$loop#00;
        assume _module.ExtensibleArray.Valid#canCall(TInt, $Heap, a#0);
        assume true;
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(127,17)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    i##0 := LitInt(570);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##0 := Call$$_module.ExtensibleArray.Get(TInt, a#0, i##0);
    havoc $rhs##0;
    assume $rhs##0 == $Unbox($tmp##0): int;
    // TrCallStmt: After ProcessCallStmt
    k#1 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(127,21)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(127,24)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(128,13)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    i##1 := LitInt(0);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##1 := Call$$_module.ExtensibleArray.Get(TInt, a#0, i##1);
    havoc $rhs##1;
    assume $rhs##1 == $Unbox($tmp##1): int;
    // TrCallStmt: After ProcessCallStmt
    k#1 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(128,15)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(128,18)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(129,13)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    i##2 := LitInt(1000);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##2 := Call$$_module.ExtensibleArray.Get(TInt, a#0, i##2);
    havoc $rhs##2;
    assume $rhs##2 == $Unbox($tmp##2): int;
    // TrCallStmt: After ProcessCallStmt
    k#1 := $rhs##2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(129,18)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(129,21)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(130,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    i##3 := LitInt(1000);
    assume true;
    // ProcessCallStmt: CheckSubrange
    t##0 := LitInt(23);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, a#0, _module.ExtensibleArray.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.ExtensibleArray.Set(TInt, a#0, i##3, $Box(t##0));
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(130,17)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(131,13)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    i##4 := LitInt(0);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##3 := Call$$_module.ExtensibleArray.Get(TInt, a#0, i##4);
    havoc $rhs##3;
    assume $rhs##3 == $Unbox($tmp##3): int;
    // TrCallStmt: After ProcessCallStmt
    k#1 := $rhs##3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(131,15)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(131,18)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(132,13)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    i##5 := LitInt(1000);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##4 := Call$$_module.ExtensibleArray.Get(TInt, a#0, i##5);
    havoc $rhs##4;
    assume $rhs##4 == $Unbox($tmp##4): int;
    // TrCallStmt: After ProcessCallStmt
    k#1 := $rhs##4;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(132,18)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(132,21)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(133,13)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    i##6 := LitInt(66000);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##5 := Call$$_module.ExtensibleArray.Get(TInt, a#0, i##6);
    havoc $rhs##5;
    assume $rhs##5 == $Unbox($tmp##5): int;
    // TrCallStmt: After ProcessCallStmt
    k#1 := $rhs##5;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(133,19)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/ExtensibleArray.dfy(133,22)
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

const unique tytagFamily$ExtensibleArray: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$Contents: NameFamily;

const unique field$Repr: NameFamily;

const unique field$elements: NameFamily;

const unique field$more: NameFamily;

const unique field$length: NameFamily;

const unique field$M: NameFamily;
