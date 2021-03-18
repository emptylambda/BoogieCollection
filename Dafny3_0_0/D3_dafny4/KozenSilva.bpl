// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy -print:./KozenSilva.bpl

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
function #_module.Stream.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.Stream.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#14#0#0, a#14#1#0) } 
  DatatypeCtorId(#_module.Stream.Cons(a#14#0#0, a#14#1#0))
     == ##_module.Stream.Cons);

function _module.Stream.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Stream.Cons_q(d) } 
  _module.Stream.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.Stream.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Stream.Cons_q(d) } 
  _module.Stream.Cons_q(d)
     ==> (exists a#15#0#0: Box, a#15#1#0: DatatypeType :: 
      d == #_module.Stream.Cons(a#15#0#0, a#15#1#0)));

function Tclass._module.Stream(Ty) : Ty;

const unique Tagclass._module.Stream: TyTag;

// Tclass._module.Stream Tag
axiom (forall _module.Stream$A: Ty :: 
  { Tclass._module.Stream(_module.Stream$A) } 
  Tag(Tclass._module.Stream(_module.Stream$A)) == Tagclass._module.Stream
     && TagFamily(Tclass._module.Stream(_module.Stream$A)) == tytagFamily$Stream);

// Tclass._module.Stream injectivity 0
axiom (forall _module.Stream$A: Ty :: 
  { Tclass._module.Stream(_module.Stream$A) } 
  Tclass._module.Stream_0(Tclass._module.Stream(_module.Stream$A))
     == _module.Stream$A);

function Tclass._module.Stream_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Stream
axiom (forall _module.Stream$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Stream(_module.Stream$A)) } 
  $IsBox(bx, Tclass._module.Stream(_module.Stream$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Stream(_module.Stream$A)));

// Constructor $Is
axiom (forall _module.Stream$A: Ty, a#16#0#0: Box, a#16#1#0: DatatypeType :: 
  { $Is(#_module.Stream.Cons(a#16#0#0, a#16#1#0), 
      Tclass._module.Stream(_module.Stream$A)) } 
  $Is(#_module.Stream.Cons(a#16#0#0, a#16#1#0), 
      Tclass._module.Stream(_module.Stream$A))
     <==> $IsBox(a#16#0#0, _module.Stream$A)
       && $Is(a#16#1#0, Tclass._module.Stream(_module.Stream$A)));

// Constructor $IsAlloc
axiom (forall _module.Stream$A: Ty, a#17#0#0: Box, a#17#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Stream.Cons(a#17#0#0, a#17#1#0), 
      Tclass._module.Stream(_module.Stream$A), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Stream.Cons(a#17#0#0, a#17#1#0), 
        Tclass._module.Stream(_module.Stream$A), 
        $h)
       <==> $IsAllocBox(a#17#0#0, _module.Stream$A, $h)
         && $IsAlloc(a#17#1#0, Tclass._module.Stream(_module.Stream$A), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Stream$A: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Stream.hd(d), _module.Stream$A, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Stream.Cons_q(d)
       && $IsAlloc(d, Tclass._module.Stream(_module.Stream$A), $h)
     ==> $IsAllocBox(_module.Stream.hd(d), _module.Stream$A, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Stream$A: Ty, $h: Heap :: 
  { $IsAlloc(_module.Stream.tl(d), Tclass._module.Stream(_module.Stream$A), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Stream.Cons_q(d)
       && $IsAlloc(d, Tclass._module.Stream(_module.Stream$A), $h)
     ==> $IsAlloc(_module.Stream.tl(d), Tclass._module.Stream(_module.Stream$A), $h));

function _module.Stream.hd(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#18#0#0: Box, a#18#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#18#0#0, a#18#1#0) } 
  _module.Stream.hd(#_module.Stream.Cons(a#18#0#0, a#18#1#0)) == a#18#0#0);

function _module.Stream.tl(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#19#0#0, a#19#1#0) } 
  _module.Stream.tl(#_module.Stream.Cons(a#19#0#0, a#19#1#0)) == a#19#1#0);

// Depth-one case-split function
function $IsA#_module.Stream(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Stream(d) } 
  $IsA#_module.Stream(d) ==> _module.Stream.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Stream$A: Ty, d: DatatypeType :: 
  { _module.Stream.Cons_q(d), $Is(d, Tclass._module.Stream(_module.Stream$A)) } 
  $Is(d, Tclass._module.Stream(_module.Stream$A)) ==> _module.Stream.Cons_q(d));

function $Eq#_module.Stream(Ty, Ty, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Stream(_module.Stream$A#l))
       && $Is(d1, Tclass._module.Stream(_module.Stream$A#r))
     ==> ($Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1)
       <==> _module.Stream.Cons_q(d0)
         && _module.Stream.Cons_q(d1)
         && (_module.Stream.Cons_q(d0) && _module.Stream.Cons_q(d1)
           ==> _module.Stream.hd(d0) == _module.Stream.hd(d1)
             && $Eq#_module.Stream(_module.Stream$A#l, 
              _module.Stream$A#r, 
              ly, 
              _module.Stream.tl(d0), 
              _module.Stream.tl(d1)))));

// Unbump layer co-equality axiom
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1) } 
  $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1)
     <==> $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, ly, d0, d1));

// Equality for codatatypes
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1) } 
  $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1)
     <==> d0 == d1);

function $PrefixEq#_module.Stream(Ty, Ty, Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Stream(_module.Stream$A#l))
       && $Is(d1, Tclass._module.Stream(_module.Stream$A#r))
     ==> ($PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> _module.Stream.Cons_q(d0)
             && _module.Stream.Cons_q(d1)
             && (_module.Stream.Cons_q(d0) && _module.Stream.Cons_q(d1)
               ==> _module.Stream.hd(d0) == _module.Stream.hd(d1)
                 && $PrefixEq#_module.Stream(_module.Stream$A#l, 
                  _module.Stream$A#r, 
                  ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  _module.Stream.tl(d0), 
                  _module.Stream.tl(d1))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k)
           ==> $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1) } 
  $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k
         ==> $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, $LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType, 
    m: Box :: 
  { $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1), $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, m, $LS(ly), d0, d1) } 
  ORD#Less(k, m)
       && $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall _module.Stream$A#l: Ty, 
    _module.Stream$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1) } 
  d0 == d1
     ==> $PrefixEq#_module.Stream(_module.Stream$A#l, _module.Stream$A#r, k, $LS(ly), d0, d1));

const unique class._module.Stream: ClassName;

// Constructor function declaration
function #_module.RecType.Bottom() : DatatypeType;

const unique ##_module.RecType.Bottom: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.RecType.Bottom()) == ##_module.RecType.Bottom;

function _module.RecType.Bottom_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.RecType.Bottom_q(d) } 
  _module.RecType.Bottom_q(d) <==> DatatypeCtorId(d) == ##_module.RecType.Bottom);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.RecType.Bottom_q(d) } 
  _module.RecType.Bottom_q(d) ==> d == #_module.RecType.Bottom());

function Tclass._module.RecType() : Ty;

const unique Tagclass._module.RecType: TyTag;

// Tclass._module.RecType Tag
axiom Tag(Tclass._module.RecType()) == Tagclass._module.RecType
   && TagFamily(Tclass._module.RecType()) == tytagFamily$RecType;

// Box/unbox axiom for Tclass._module.RecType
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.RecType()) } 
  $IsBox(bx, Tclass._module.RecType())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.RecType()));

// Constructor $Is
axiom $Is(#_module.RecType.Bottom(), Tclass._module.RecType());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.RecType.Bottom(), Tclass._module.RecType(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.RecType.Bottom(), Tclass._module.RecType(), $h));

// Constructor function declaration
function #_module.RecType.Top() : DatatypeType;

const unique ##_module.RecType.Top: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.RecType.Top()) == ##_module.RecType.Top;

function _module.RecType.Top_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.RecType.Top_q(d) } 
  _module.RecType.Top_q(d) <==> DatatypeCtorId(d) == ##_module.RecType.Top);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.RecType.Top_q(d) } 
  _module.RecType.Top_q(d) ==> d == #_module.RecType.Top());

// Constructor $Is
axiom $Is(#_module.RecType.Top(), Tclass._module.RecType());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.RecType.Top(), Tclass._module.RecType(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.RecType.Top(), Tclass._module.RecType(), $h));

// Constructor function declaration
function #_module.RecType.Arrow(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.RecType.Arrow: DtCtorId;

// Constructor identifier
axiom (forall a#28#0#0: DatatypeType, a#28#1#0: DatatypeType :: 
  { #_module.RecType.Arrow(a#28#0#0, a#28#1#0) } 
  DatatypeCtorId(#_module.RecType.Arrow(a#28#0#0, a#28#1#0))
     == ##_module.RecType.Arrow);

function _module.RecType.Arrow_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.RecType.Arrow_q(d) } 
  _module.RecType.Arrow_q(d) <==> DatatypeCtorId(d) == ##_module.RecType.Arrow);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.RecType.Arrow_q(d) } 
  _module.RecType.Arrow_q(d)
     ==> (exists a#29#0#0: DatatypeType, a#29#1#0: DatatypeType :: 
      d == #_module.RecType.Arrow(a#29#0#0, a#29#1#0)));

// Constructor $Is
axiom (forall a#30#0#0: DatatypeType, a#30#1#0: DatatypeType :: 
  { $Is(#_module.RecType.Arrow(a#30#0#0, a#30#1#0), Tclass._module.RecType()) } 
  $Is(#_module.RecType.Arrow(a#30#0#0, a#30#1#0), Tclass._module.RecType())
     <==> $Is(a#30#0#0, Tclass._module.RecType())
       && $Is(a#30#1#0, Tclass._module.RecType()));

// Constructor $IsAlloc
axiom (forall a#31#0#0: DatatypeType, a#31#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.RecType.Arrow(a#31#0#0, a#31#1#0), Tclass._module.RecType(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.RecType.Arrow(a#31#0#0, a#31#1#0), Tclass._module.RecType(), $h)
       <==> $IsAlloc(a#31#0#0, Tclass._module.RecType(), $h)
         && $IsAlloc(a#31#1#0, Tclass._module.RecType(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.RecType.dom(d), Tclass._module.RecType(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.RecType.Arrow_q(d)
       && $IsAlloc(d, Tclass._module.RecType(), $h)
     ==> $IsAlloc(_module.RecType.dom(d), Tclass._module.RecType(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.RecType.ran(d), Tclass._module.RecType(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.RecType.Arrow_q(d)
       && $IsAlloc(d, Tclass._module.RecType(), $h)
     ==> $IsAlloc(_module.RecType.ran(d), Tclass._module.RecType(), $h));

function _module.RecType.dom(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#32#0#0: DatatypeType, a#32#1#0: DatatypeType :: 
  { #_module.RecType.Arrow(a#32#0#0, a#32#1#0) } 
  _module.RecType.dom(#_module.RecType.Arrow(a#32#0#0, a#32#1#0)) == a#32#0#0);

function _module.RecType.ran(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#33#0#0: DatatypeType, a#33#1#0: DatatypeType :: 
  { #_module.RecType.Arrow(a#33#0#0, a#33#1#0) } 
  _module.RecType.ran(#_module.RecType.Arrow(a#33#0#0, a#33#1#0)) == a#33#1#0);

// Depth-one case-split function
function $IsA#_module.RecType(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.RecType(d) } 
  $IsA#_module.RecType(d)
     ==> _module.RecType.Bottom_q(d)
       || _module.RecType.Top_q(d)
       || _module.RecType.Arrow_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.RecType.Arrow_q(d), $Is(d, Tclass._module.RecType()) } 
    { _module.RecType.Top_q(d), $Is(d, Tclass._module.RecType()) } 
    { _module.RecType.Bottom_q(d), $Is(d, Tclass._module.RecType()) } 
  $Is(d, Tclass._module.RecType())
     ==> _module.RecType.Bottom_q(d)
       || _module.RecType.Top_q(d)
       || _module.RecType.Arrow_q(d));

function $Eq#_module.RecType(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.RecType($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.RecType()) && $Is(d1, Tclass._module.RecType())
     ==> ($Eq#_module.RecType($LS(ly), d0, d1)
       <==> (_module.RecType.Bottom_q(d0) && _module.RecType.Bottom_q(d1))
         || (_module.RecType.Top_q(d0) && _module.RecType.Top_q(d1))
         || (
          _module.RecType.Arrow_q(d0)
           && _module.RecType.Arrow_q(d1)
           && (_module.RecType.Arrow_q(d0) && _module.RecType.Arrow_q(d1)
             ==> $Eq#_module.RecType(ly, _module.RecType.dom(d0), _module.RecType.dom(d1))
               && $Eq#_module.RecType(ly, _module.RecType.ran(d0), _module.RecType.ran(d1))))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.RecType($LS(ly), d0, d1) } 
  $Eq#_module.RecType($LS(ly), d0, d1) <==> $Eq#_module.RecType(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.RecType($LS(ly), d0, d1) } 
  $Eq#_module.RecType($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.RecType(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.RecType(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.RecType()) && $Is(d1, Tclass._module.RecType())
     ==> ($PrefixEq#_module.RecType(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (_module.RecType.Bottom_q(d0) && _module.RecType.Bottom_q(d1))
             || (_module.RecType.Top_q(d0) && _module.RecType.Top_q(d1))
             || (
              _module.RecType.Arrow_q(d0)
               && _module.RecType.Arrow_q(d1)
               && (_module.RecType.Arrow_q(d0) && _module.RecType.Arrow_q(d1)
                 ==> $PrefixEq#_module.RecType(ORD#Minus(k, ORD#FromNat(1)), 
                    ly, 
                    _module.RecType.dom(d0), 
                    _module.RecType.dom(d1))
                   && $PrefixEq#_module.RecType(ORD#Minus(k, ORD#FromNat(1)), 
                    ly, 
                    _module.RecType.ran(d0), 
                    _module.RecType.ran(d1)))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.RecType(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.RecType(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.RecType(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.RecType(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.RecType($LS(ly), d0, d1) } 
  $Eq#_module.RecType($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.RecType(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.RecType(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.RecType($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.RecType(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.RecType(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.RecType($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.RecType(k, $LS(ly), d0, d1), $PrefixEq#_module.RecType(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.RecType(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.RecType(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.RecType(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.RecType(k, $LS(ly), d0, d1));

const unique class._module.RecType: ClassName;

const #$Const: Ty;

const unique class._module.Const: ClassName;

const #$Var: Ty;

const unique class._module.Var: ClassName;

// Constructor function declaration
function #_module.Term.TermConst(Box) : DatatypeType;

const unique ##_module.Term.TermConst: DtCtorId;

// Constructor identifier
axiom (forall a#34#0#0: Box :: 
  { #_module.Term.TermConst(a#34#0#0) } 
  DatatypeCtorId(#_module.Term.TermConst(a#34#0#0)) == ##_module.Term.TermConst);

function _module.Term.TermConst_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Term.TermConst_q(d) } 
  _module.Term.TermConst_q(d) <==> DatatypeCtorId(d) == ##_module.Term.TermConst);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Term.TermConst_q(d) } 
  _module.Term.TermConst_q(d)
     ==> (exists a#35#0#0: Box :: d == #_module.Term.TermConst(a#35#0#0)));

function Tclass._module.Term() : Ty;

const unique Tagclass._module.Term: TyTag;

// Tclass._module.Term Tag
axiom Tag(Tclass._module.Term()) == Tagclass._module.Term
   && TagFamily(Tclass._module.Term()) == tytagFamily$Term;

// Box/unbox axiom for Tclass._module.Term
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Term()) } 
  $IsBox(bx, Tclass._module.Term())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Term()));

// Constructor $Is
axiom (forall a#36#0#0: Box :: 
  { $Is(#_module.Term.TermConst(a#36#0#0), Tclass._module.Term()) } 
  $Is(#_module.Term.TermConst(a#36#0#0), Tclass._module.Term())
     <==> $IsBox(a#36#0#0, #$Const));

// Constructor $IsAlloc
axiom (forall a#37#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Term.TermConst(a#37#0#0), Tclass._module.Term(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Term.TermConst(a#37#0#0), Tclass._module.Term(), $h)
       <==> $IsAllocBox(a#37#0#0, #$Const, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAllocBox(_module.Term._h0(d), #$Const, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Term.TermConst_q(d)
       && $IsAlloc(d, Tclass._module.Term(), $h)
     ==> $IsAllocBox(_module.Term._h0(d), #$Const, $h));

// Constructor literal
axiom (forall a#38#0#0: Box :: 
  { #_module.Term.TermConst(Lit(a#38#0#0)) } 
  #_module.Term.TermConst(Lit(a#38#0#0)) == Lit(#_module.Term.TermConst(a#38#0#0)));

function _module.Term._h0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#39#0#0: Box :: 
  { #_module.Term.TermConst(a#39#0#0) } 
  _module.Term._h0(#_module.Term.TermConst(a#39#0#0)) == a#39#0#0);

// Inductive rank
axiom (forall a#40#0#0: Box :: 
  { #_module.Term.TermConst(a#40#0#0) } 
  BoxRank(a#40#0#0) < DtRank(#_module.Term.TermConst(a#40#0#0)));

// Constructor function declaration
function #_module.Term.TermVar(Box) : DatatypeType;

const unique ##_module.Term.TermVar: DtCtorId;

// Constructor identifier
axiom (forall a#41#0#0: Box :: 
  { #_module.Term.TermVar(a#41#0#0) } 
  DatatypeCtorId(#_module.Term.TermVar(a#41#0#0)) == ##_module.Term.TermVar);

function _module.Term.TermVar_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Term.TermVar_q(d) } 
  _module.Term.TermVar_q(d) <==> DatatypeCtorId(d) == ##_module.Term.TermVar);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Term.TermVar_q(d) } 
  _module.Term.TermVar_q(d)
     ==> (exists a#42#0#0: Box :: d == #_module.Term.TermVar(a#42#0#0)));

// Constructor $Is
axiom (forall a#43#0#0: Box :: 
  { $Is(#_module.Term.TermVar(a#43#0#0), Tclass._module.Term()) } 
  $Is(#_module.Term.TermVar(a#43#0#0), Tclass._module.Term())
     <==> $IsBox(a#43#0#0, #$Var));

// Constructor $IsAlloc
axiom (forall a#44#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Term.TermVar(a#44#0#0), Tclass._module.Term(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Term.TermVar(a#44#0#0), Tclass._module.Term(), $h)
       <==> $IsAllocBox(a#44#0#0, #$Var, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAllocBox(_module.Term._h1(d), #$Var, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Term.TermVar_q(d)
       && $IsAlloc(d, Tclass._module.Term(), $h)
     ==> $IsAllocBox(_module.Term._h1(d), #$Var, $h));

// Constructor literal
axiom (forall a#45#0#0: Box :: 
  { #_module.Term.TermVar(Lit(a#45#0#0)) } 
  #_module.Term.TermVar(Lit(a#45#0#0)) == Lit(#_module.Term.TermVar(a#45#0#0)));

function _module.Term._h1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#46#0#0: Box :: 
  { #_module.Term.TermVar(a#46#0#0) } 
  _module.Term._h1(#_module.Term.TermVar(a#46#0#0)) == a#46#0#0);

// Inductive rank
axiom (forall a#47#0#0: Box :: 
  { #_module.Term.TermVar(a#47#0#0) } 
  BoxRank(a#47#0#0) < DtRank(#_module.Term.TermVar(a#47#0#0)));

// Constructor function declaration
function #_module.Term.TermAbs(DatatypeType) : DatatypeType;

const unique ##_module.Term.TermAbs: DtCtorId;

// Constructor identifier
axiom (forall a#48#0#0: DatatypeType :: 
  { #_module.Term.TermAbs(a#48#0#0) } 
  DatatypeCtorId(#_module.Term.TermAbs(a#48#0#0)) == ##_module.Term.TermAbs);

function _module.Term.TermAbs_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Term.TermAbs_q(d) } 
  _module.Term.TermAbs_q(d) <==> DatatypeCtorId(d) == ##_module.Term.TermAbs);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Term.TermAbs_q(d) } 
  _module.Term.TermAbs_q(d)
     ==> (exists a#49#0#0: DatatypeType :: d == #_module.Term.TermAbs(a#49#0#0)));

function Tclass._module.LambdaAbs() : Ty;

const unique Tagclass._module.LambdaAbs: TyTag;

// Tclass._module.LambdaAbs Tag
axiom Tag(Tclass._module.LambdaAbs()) == Tagclass._module.LambdaAbs
   && TagFamily(Tclass._module.LambdaAbs()) == tytagFamily$LambdaAbs;

// Box/unbox axiom for Tclass._module.LambdaAbs
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.LambdaAbs()) } 
  $IsBox(bx, Tclass._module.LambdaAbs())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.LambdaAbs()));

// Constructor $Is
axiom (forall a#50#0#0: DatatypeType :: 
  { $Is(#_module.Term.TermAbs(a#50#0#0), Tclass._module.Term()) } 
  $Is(#_module.Term.TermAbs(a#50#0#0), Tclass._module.Term())
     <==> $Is(a#50#0#0, Tclass._module.LambdaAbs()));

// Constructor $IsAlloc
axiom (forall a#51#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Term.TermAbs(a#51#0#0), Tclass._module.Term(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Term.TermAbs(a#51#0#0), Tclass._module.Term(), $h)
       <==> $IsAlloc(a#51#0#0, Tclass._module.LambdaAbs(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Term.abs(d), Tclass._module.LambdaAbs(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Term.TermAbs_q(d)
       && $IsAlloc(d, Tclass._module.Term(), $h)
     ==> $IsAlloc(_module.Term.abs(d), Tclass._module.LambdaAbs(), $h));

// Constructor literal
axiom (forall a#52#0#0: DatatypeType :: 
  { #_module.Term.TermAbs(Lit(a#52#0#0)) } 
  #_module.Term.TermAbs(Lit(a#52#0#0)) == Lit(#_module.Term.TermAbs(a#52#0#0)));

function _module.Term.abs(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#53#0#0: DatatypeType :: 
  { #_module.Term.TermAbs(a#53#0#0) } 
  _module.Term.abs(#_module.Term.TermAbs(a#53#0#0)) == a#53#0#0);

// Inductive rank
axiom (forall a#54#0#0: DatatypeType :: 
  { #_module.Term.TermAbs(a#54#0#0) } 
  DtRank(a#54#0#0) < DtRank(#_module.Term.TermAbs(a#54#0#0)));

// Depth-one case-split function
function $IsA#_module.Term(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Term(d) } 
  $IsA#_module.Term(d)
     ==> _module.Term.TermConst_q(d)
       || _module.Term.TermVar_q(d)
       || _module.Term.TermAbs_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Term.TermAbs_q(d), $Is(d, Tclass._module.Term()) } 
    { _module.Term.TermVar_q(d), $Is(d, Tclass._module.Term()) } 
    { _module.Term.TermConst_q(d), $Is(d, Tclass._module.Term()) } 
  $Is(d, Tclass._module.Term())
     ==> _module.Term.TermConst_q(d)
       || _module.Term.TermVar_q(d)
       || _module.Term.TermAbs_q(d));

// Datatype extensional equality declaration
function _module.Term#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Term.TermConst
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Term#Equal(a, b), _module.Term.TermConst_q(a) } 
    { _module.Term#Equal(a, b), _module.Term.TermConst_q(b) } 
  _module.Term.TermConst_q(a) && _module.Term.TermConst_q(b)
     ==> (_module.Term#Equal(a, b) <==> _module.Term._h0(a) == _module.Term._h0(b)));

// Datatype extensional equality definition: #_module.Term.TermVar
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Term#Equal(a, b), _module.Term.TermVar_q(a) } 
    { _module.Term#Equal(a, b), _module.Term.TermVar_q(b) } 
  _module.Term.TermVar_q(a) && _module.Term.TermVar_q(b)
     ==> (_module.Term#Equal(a, b) <==> _module.Term._h1(a) == _module.Term._h1(b)));

// Datatype extensional equality definition: #_module.Term.TermAbs
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Term#Equal(a, b), _module.Term.TermAbs_q(a) } 
    { _module.Term#Equal(a, b), _module.Term.TermAbs_q(b) } 
  _module.Term.TermAbs_q(a) && _module.Term.TermAbs_q(b)
     ==> (_module.Term#Equal(a, b)
       <==> _module.LambdaAbs#Equal(_module.Term.abs(a), _module.Term.abs(b))));

// Datatype extensionality axiom: _module.Term
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Term#Equal(a, b) } 
  _module.Term#Equal(a, b) <==> a == b);

const unique class._module.Term: ClassName;

// Constructor function declaration
function #_module.LambdaAbs.Fun(Box, DatatypeType) : DatatypeType;

const unique ##_module.LambdaAbs.Fun: DtCtorId;

// Constructor identifier
axiom (forall a#55#0#0: Box, a#55#1#0: DatatypeType :: 
  { #_module.LambdaAbs.Fun(a#55#0#0, a#55#1#0) } 
  DatatypeCtorId(#_module.LambdaAbs.Fun(a#55#0#0, a#55#1#0))
     == ##_module.LambdaAbs.Fun);

function _module.LambdaAbs.Fun_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.LambdaAbs.Fun_q(d) } 
  _module.LambdaAbs.Fun_q(d) <==> DatatypeCtorId(d) == ##_module.LambdaAbs.Fun);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.LambdaAbs.Fun_q(d) } 
  _module.LambdaAbs.Fun_q(d)
     ==> (exists a#56#0#0: Box, a#56#1#0: DatatypeType :: 
      d == #_module.LambdaAbs.Fun(a#56#0#0, a#56#1#0)));

// Constructor $Is
axiom (forall a#57#0#0: Box, a#57#1#0: DatatypeType :: 
  { $Is(#_module.LambdaAbs.Fun(a#57#0#0, a#57#1#0), Tclass._module.LambdaAbs()) } 
  $Is(#_module.LambdaAbs.Fun(a#57#0#0, a#57#1#0), Tclass._module.LambdaAbs())
     <==> $IsBox(a#57#0#0, #$Var) && $Is(a#57#1#0, Tclass._module.Term()));

// Constructor $IsAlloc
axiom (forall a#58#0#0: Box, a#58#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.LambdaAbs.Fun(a#58#0#0, a#58#1#0), Tclass._module.LambdaAbs(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.LambdaAbs.Fun(a#58#0#0, a#58#1#0), Tclass._module.LambdaAbs(), $h)
       <==> $IsAllocBox(a#58#0#0, #$Var, $h)
         && $IsAlloc(a#58#1#0, Tclass._module.Term(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAllocBox(_module.LambdaAbs.v(d), #$Var, $h) } 
  $IsGoodHeap($h)
       && 
      _module.LambdaAbs.Fun_q(d)
       && $IsAlloc(d, Tclass._module.LambdaAbs(), $h)
     ==> $IsAllocBox(_module.LambdaAbs.v(d), #$Var, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.LambdaAbs.body(d), Tclass._module.Term(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.LambdaAbs.Fun_q(d)
       && $IsAlloc(d, Tclass._module.LambdaAbs(), $h)
     ==> $IsAlloc(_module.LambdaAbs.body(d), Tclass._module.Term(), $h));

// Constructor literal
axiom (forall a#59#0#0: Box, a#59#1#0: DatatypeType :: 
  { #_module.LambdaAbs.Fun(Lit(a#59#0#0), Lit(a#59#1#0)) } 
  #_module.LambdaAbs.Fun(Lit(a#59#0#0), Lit(a#59#1#0))
     == Lit(#_module.LambdaAbs.Fun(a#59#0#0, a#59#1#0)));

function _module.LambdaAbs.v(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#60#0#0: Box, a#60#1#0: DatatypeType :: 
  { #_module.LambdaAbs.Fun(a#60#0#0, a#60#1#0) } 
  _module.LambdaAbs.v(#_module.LambdaAbs.Fun(a#60#0#0, a#60#1#0)) == a#60#0#0);

// Inductive rank
axiom (forall a#61#0#0: Box, a#61#1#0: DatatypeType :: 
  { #_module.LambdaAbs.Fun(a#61#0#0, a#61#1#0) } 
  BoxRank(a#61#0#0) < DtRank(#_module.LambdaAbs.Fun(a#61#0#0, a#61#1#0)));

function _module.LambdaAbs.body(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#62#0#0: Box, a#62#1#0: DatatypeType :: 
  { #_module.LambdaAbs.Fun(a#62#0#0, a#62#1#0) } 
  _module.LambdaAbs.body(#_module.LambdaAbs.Fun(a#62#0#0, a#62#1#0)) == a#62#1#0);

// Inductive rank
axiom (forall a#63#0#0: Box, a#63#1#0: DatatypeType :: 
  { #_module.LambdaAbs.Fun(a#63#0#0, a#63#1#0) } 
  DtRank(a#63#1#0) < DtRank(#_module.LambdaAbs.Fun(a#63#0#0, a#63#1#0)));

// Depth-one case-split function
function $IsA#_module.LambdaAbs(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.LambdaAbs(d) } 
  $IsA#_module.LambdaAbs(d) ==> _module.LambdaAbs.Fun_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.LambdaAbs.Fun_q(d), $Is(d, Tclass._module.LambdaAbs()) } 
  $Is(d, Tclass._module.LambdaAbs()) ==> _module.LambdaAbs.Fun_q(d));

// Datatype extensional equality declaration
function _module.LambdaAbs#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.LambdaAbs.Fun
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.LambdaAbs#Equal(a, b) } 
  true
     ==> (_module.LambdaAbs#Equal(a, b)
       <==> _module.LambdaAbs.v(a) == _module.LambdaAbs.v(b)
         && _module.Term#Equal(_module.LambdaAbs.body(a), _module.LambdaAbs.body(b))));

// Datatype extensionality axiom: _module.LambdaAbs
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.LambdaAbs#Equal(a, b) } 
  _module.LambdaAbs#Equal(a, b) <==> a == b);

const unique class._module.LambdaAbs: ClassName;

// Constructor function declaration
function #_module.Val.ValConst(Box) : DatatypeType;

const unique ##_module.Val.ValConst: DtCtorId;

// Constructor identifier
axiom (forall a#64#0#0: Box :: 
  { #_module.Val.ValConst(a#64#0#0) } 
  DatatypeCtorId(#_module.Val.ValConst(a#64#0#0)) == ##_module.Val.ValConst);

function _module.Val.ValConst_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Val.ValConst_q(d) } 
  _module.Val.ValConst_q(d) <==> DatatypeCtorId(d) == ##_module.Val.ValConst);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Val.ValConst_q(d) } 
  _module.Val.ValConst_q(d)
     ==> (exists a#65#0#0: Box :: d == #_module.Val.ValConst(a#65#0#0)));

function Tclass._module.Val() : Ty;

const unique Tagclass._module.Val: TyTag;

// Tclass._module.Val Tag
axiom Tag(Tclass._module.Val()) == Tagclass._module.Val
   && TagFamily(Tclass._module.Val()) == tytagFamily$Val;

// Box/unbox axiom for Tclass._module.Val
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Val()) } 
  $IsBox(bx, Tclass._module.Val())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Val()));

// Constructor $Is
axiom (forall a#66#0#0: Box :: 
  { $Is(#_module.Val.ValConst(a#66#0#0), Tclass._module.Val()) } 
  $Is(#_module.Val.ValConst(a#66#0#0), Tclass._module.Val())
     <==> $IsBox(a#66#0#0, #$Const));

// Constructor $IsAlloc
axiom (forall a#67#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Val.ValConst(a#67#0#0), Tclass._module.Val(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Val.ValConst(a#67#0#0), Tclass._module.Val(), $h)
       <==> $IsAllocBox(a#67#0#0, #$Const, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAllocBox(_module.Val._h2(d), #$Const, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Val.ValConst_q(d)
       && $IsAlloc(d, Tclass._module.Val(), $h)
     ==> $IsAllocBox(_module.Val._h2(d), #$Const, $h));

function _module.Val._h2(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#68#0#0: Box :: 
  { #_module.Val.ValConst(a#68#0#0) } 
  _module.Val._h2(#_module.Val.ValConst(a#68#0#0)) == a#68#0#0);

// Constructor function declaration
function #_module.Val.ValCl(DatatypeType) : DatatypeType;

const unique ##_module.Val.ValCl: DtCtorId;

// Constructor identifier
axiom (forall a#69#0#0: DatatypeType :: 
  { #_module.Val.ValCl(a#69#0#0) } 
  DatatypeCtorId(#_module.Val.ValCl(a#69#0#0)) == ##_module.Val.ValCl);

function _module.Val.ValCl_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Val.ValCl_q(d) } 
  _module.Val.ValCl_q(d) <==> DatatypeCtorId(d) == ##_module.Val.ValCl);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Val.ValCl_q(d) } 
  _module.Val.ValCl_q(d)
     ==> (exists a#70#0#0: DatatypeType :: d == #_module.Val.ValCl(a#70#0#0)));

function Tclass._module.Cl() : Ty;

const unique Tagclass._module.Cl: TyTag;

// Tclass._module.Cl Tag
axiom Tag(Tclass._module.Cl()) == Tagclass._module.Cl
   && TagFamily(Tclass._module.Cl()) == tytagFamily$Cl;

// Box/unbox axiom for Tclass._module.Cl
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cl()) } 
  $IsBox(bx, Tclass._module.Cl())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Cl()));

// Constructor $Is
axiom (forall a#71#0#0: DatatypeType :: 
  { $Is(#_module.Val.ValCl(a#71#0#0), Tclass._module.Val()) } 
  $Is(#_module.Val.ValCl(a#71#0#0), Tclass._module.Val())
     <==> $Is(a#71#0#0, Tclass._module.Cl()));

// Constructor $IsAlloc
axiom (forall a#72#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Val.ValCl(a#72#0#0), Tclass._module.Val(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Val.ValCl(a#72#0#0), Tclass._module.Val(), $h)
       <==> $IsAlloc(a#72#0#0, Tclass._module.Cl(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Val.cl(d), Tclass._module.Cl(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Val.ValCl_q(d)
       && $IsAlloc(d, Tclass._module.Val(), $h)
     ==> $IsAlloc(_module.Val.cl(d), Tclass._module.Cl(), $h));

function _module.Val.cl(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#73#0#0: DatatypeType :: 
  { #_module.Val.ValCl(a#73#0#0) } 
  _module.Val.cl(#_module.Val.ValCl(a#73#0#0)) == a#73#0#0);

// Depth-one case-split function
function $IsA#_module.Val(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Val(d) } 
  $IsA#_module.Val(d) ==> _module.Val.ValConst_q(d) || _module.Val.ValCl_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Val.ValCl_q(d), $Is(d, Tclass._module.Val()) } 
    { _module.Val.ValConst_q(d), $Is(d, Tclass._module.Val()) } 
  $Is(d, Tclass._module.Val())
     ==> _module.Val.ValConst_q(d) || _module.Val.ValCl_q(d));

function $Eq#_module.Val(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Val($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Val()) && $Is(d1, Tclass._module.Val())
     ==> ($Eq#_module.Val($LS(ly), d0, d1)
       <==> (
          _module.Val.ValConst_q(d0)
           && _module.Val.ValConst_q(d1)
           && (_module.Val.ValConst_q(d0) && _module.Val.ValConst_q(d1)
             ==> _module.Val._h2(d0) == _module.Val._h2(d1)))
         || (
          _module.Val.ValCl_q(d0)
           && _module.Val.ValCl_q(d1)
           && (_module.Val.ValCl_q(d0) && _module.Val.ValCl_q(d1)
             ==> $Eq#_module.Cl($LS($LS($LZ)), _module.Val.cl(d0), _module.Val.cl(d1))))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Val($LS(ly), d0, d1) } 
  $Eq#_module.Val($LS(ly), d0, d1) <==> $Eq#_module.Val(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Val($LS(ly), d0, d1) } 
  $Eq#_module.Val($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.Val(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Val(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Val()) && $Is(d1, Tclass._module.Val())
     ==> ($PrefixEq#_module.Val(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (
              _module.Val.ValConst_q(d0)
               && _module.Val.ValConst_q(d1)
               && (_module.Val.ValConst_q(d0) && _module.Val.ValConst_q(d1)
                 ==> _module.Val._h2(d0) == _module.Val._h2(d1)))
             || (
              _module.Val.ValCl_q(d0)
               && _module.Val.ValCl_q(d1)
               && (_module.Val.ValCl_q(d0) && _module.Val.ValCl_q(d1)
                 ==> $Eq#_module.Cl($LS($LS($LZ)), _module.Val.cl(d0), _module.Val.cl(d1)))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.Val(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Val(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.Val(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.Val(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Val($LS(ly), d0, d1) } 
  $Eq#_module.Val($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.Val(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.Val(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Val($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.Val(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.Val(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.Val($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.Val(k, $LS(ly), d0, d1), $PrefixEq#_module.Val(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.Val(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.Val(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Val(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.Val(k, $LS(ly), d0, d1));

const unique class._module.Val: ClassName;

// Constructor function declaration
function #_module.Cl.Closure(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Cl.Closure: DtCtorId;

// Constructor identifier
axiom (forall a#74#0#0: DatatypeType, a#74#1#0: DatatypeType :: 
  { #_module.Cl.Closure(a#74#0#0, a#74#1#0) } 
  DatatypeCtorId(#_module.Cl.Closure(a#74#0#0, a#74#1#0)) == ##_module.Cl.Closure);

function _module.Cl.Closure_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Cl.Closure_q(d) } 
  _module.Cl.Closure_q(d) <==> DatatypeCtorId(d) == ##_module.Cl.Closure);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Cl.Closure_q(d) } 
  _module.Cl.Closure_q(d)
     ==> (exists a#75#0#0: DatatypeType, a#75#1#0: DatatypeType :: 
      d == #_module.Cl.Closure(a#75#0#0, a#75#1#0)));

function Tclass._module.ClEnv() : Ty;

const unique Tagclass._module.ClEnv: TyTag;

// Tclass._module.ClEnv Tag
axiom Tag(Tclass._module.ClEnv()) == Tagclass._module.ClEnv
   && TagFamily(Tclass._module.ClEnv()) == tytagFamily$ClEnv;

// Box/unbox axiom for Tclass._module.ClEnv
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ClEnv()) } 
  $IsBox(bx, Tclass._module.ClEnv())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.ClEnv()));

// Constructor $Is
axiom (forall a#76#0#0: DatatypeType, a#76#1#0: DatatypeType :: 
  { $Is(#_module.Cl.Closure(a#76#0#0, a#76#1#0), Tclass._module.Cl()) } 
  $Is(#_module.Cl.Closure(a#76#0#0, a#76#1#0), Tclass._module.Cl())
     <==> $Is(a#76#0#0, Tclass._module.LambdaAbs())
       && $Is(a#76#1#0, Tclass._module.ClEnv()));

// Constructor $IsAlloc
axiom (forall a#77#0#0: DatatypeType, a#77#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Cl.Closure(a#77#0#0, a#77#1#0), Tclass._module.Cl(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Cl.Closure(a#77#0#0, a#77#1#0), Tclass._module.Cl(), $h)
       <==> $IsAlloc(a#77#0#0, Tclass._module.LambdaAbs(), $h)
         && $IsAlloc(a#77#1#0, Tclass._module.ClEnv(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Cl.abs(d), Tclass._module.LambdaAbs(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Cl.Closure_q(d)
       && $IsAlloc(d, Tclass._module.Cl(), $h)
     ==> $IsAlloc(_module.Cl.abs(d), Tclass._module.LambdaAbs(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Cl.env(d), Tclass._module.ClEnv(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Cl.Closure_q(d)
       && $IsAlloc(d, Tclass._module.Cl(), $h)
     ==> $IsAlloc(_module.Cl.env(d), Tclass._module.ClEnv(), $h));

function _module.Cl.abs(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#78#0#0: DatatypeType, a#78#1#0: DatatypeType :: 
  { #_module.Cl.Closure(a#78#0#0, a#78#1#0) } 
  _module.Cl.abs(#_module.Cl.Closure(a#78#0#0, a#78#1#0)) == a#78#0#0);

function _module.Cl.env(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#79#0#0: DatatypeType, a#79#1#0: DatatypeType :: 
  { #_module.Cl.Closure(a#79#0#0, a#79#1#0) } 
  _module.Cl.env(#_module.Cl.Closure(a#79#0#0, a#79#1#0)) == a#79#1#0);

// Depth-one case-split function
function $IsA#_module.Cl(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Cl(d) } 
  $IsA#_module.Cl(d) ==> _module.Cl.Closure_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Cl.Closure_q(d), $Is(d, Tclass._module.Cl()) } 
  $Is(d, Tclass._module.Cl()) ==> _module.Cl.Closure_q(d));

function $Eq#_module.Cl(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Cl($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Cl()) && $Is(d1, Tclass._module.Cl())
     ==> ($Eq#_module.Cl($LS(ly), d0, d1)
       <==> _module.Cl.Closure_q(d0)
         && _module.Cl.Closure_q(d1)
         && (_module.Cl.Closure_q(d0) && _module.Cl.Closure_q(d1)
           ==> _module.LambdaAbs#Equal(_module.Cl.abs(d0), _module.Cl.abs(d1))
             && $Eq#_module.ClEnv($LS($LS($LZ)), _module.Cl.env(d0), _module.Cl.env(d1)))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Cl($LS(ly), d0, d1) } 
  $Eq#_module.Cl($LS(ly), d0, d1) <==> $Eq#_module.Cl(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Cl($LS(ly), d0, d1) } 
  $Eq#_module.Cl($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.Cl(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Cl(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Cl()) && $Is(d1, Tclass._module.Cl())
     ==> ($PrefixEq#_module.Cl(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> _module.Cl.Closure_q(d0)
             && _module.Cl.Closure_q(d1)
             && (_module.Cl.Closure_q(d0) && _module.Cl.Closure_q(d1)
               ==> _module.LambdaAbs#Equal(_module.Cl.abs(d0), _module.Cl.abs(d1))
                 && $Eq#_module.ClEnv($LS($LS($LZ)), _module.Cl.env(d0), _module.Cl.env(d1))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.Cl(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Cl(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.Cl(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.Cl(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Cl($LS(ly), d0, d1) } 
  $Eq#_module.Cl($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.Cl(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.Cl(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Cl($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.Cl(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.Cl(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.Cl($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.Cl(k, $LS(ly), d0, d1), $PrefixEq#_module.Cl(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.Cl(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.Cl(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Cl(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.Cl(k, $LS(ly), d0, d1));

const unique class._module.Cl: ClassName;

// Constructor function declaration
function #_module.ClEnv.ClEnvironment(Map Box Box) : DatatypeType;

const unique ##_module.ClEnv.ClEnvironment: DtCtorId;

// Constructor identifier
axiom (forall a#80#0#0: Map Box Box :: 
  { #_module.ClEnv.ClEnvironment(a#80#0#0) } 
  DatatypeCtorId(#_module.ClEnv.ClEnvironment(a#80#0#0))
     == ##_module.ClEnv.ClEnvironment);

function _module.ClEnv.ClEnvironment_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.ClEnv.ClEnvironment_q(d) } 
  _module.ClEnv.ClEnvironment_q(d)
     <==> DatatypeCtorId(d) == ##_module.ClEnv.ClEnvironment);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.ClEnv.ClEnvironment_q(d) } 
  _module.ClEnv.ClEnvironment_q(d)
     ==> (exists a#81#0#0: Map Box Box :: d == #_module.ClEnv.ClEnvironment(a#81#0#0)));

// Constructor $Is
axiom (forall a#82#0#0: Map Box Box :: 
  { $Is(#_module.ClEnv.ClEnvironment(a#82#0#0), Tclass._module.ClEnv()) } 
  $Is(#_module.ClEnv.ClEnvironment(a#82#0#0), Tclass._module.ClEnv())
     <==> $Is(a#82#0#0, TMap(#$Var, Tclass._module.Val())));

// Constructor $IsAlloc
axiom (forall a#83#0#0: Map Box Box, $h: Heap :: 
  { $IsAlloc(#_module.ClEnv.ClEnvironment(a#83#0#0), Tclass._module.ClEnv(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.ClEnv.ClEnvironment(a#83#0#0), Tclass._module.ClEnv(), $h)
       <==> $IsAlloc(a#83#0#0, TMap(#$Var, Tclass._module.Val()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.ClEnv.m(d), TMap(#$Var, Tclass._module.Val()), $h) } 
  $IsGoodHeap($h)
       && 
      _module.ClEnv.ClEnvironment_q(d)
       && $IsAlloc(d, Tclass._module.ClEnv(), $h)
     ==> $IsAlloc(_module.ClEnv.m(d), TMap(#$Var, Tclass._module.Val()), $h));

function _module.ClEnv.m(DatatypeType) : Map Box Box;

// Constructor injectivity
axiom (forall a#84#0#0: Map Box Box :: 
  { #_module.ClEnv.ClEnvironment(a#84#0#0) } 
  _module.ClEnv.m(#_module.ClEnv.ClEnvironment(a#84#0#0)) == a#84#0#0);

// Depth-one case-split function
function $IsA#_module.ClEnv(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.ClEnv(d) } 
  $IsA#_module.ClEnv(d) ==> _module.ClEnv.ClEnvironment_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.ClEnv.ClEnvironment_q(d), $Is(d, Tclass._module.ClEnv()) } 
  $Is(d, Tclass._module.ClEnv()) ==> _module.ClEnv.ClEnvironment_q(d));

function $Eq#_module.ClEnv(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.ClEnv($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.ClEnv()) && $Is(d1, Tclass._module.ClEnv())
     ==> ($Eq#_module.ClEnv($LS(ly), d0, d1)
       <==> _module.ClEnv.ClEnvironment_q(d0)
         && _module.ClEnv.ClEnvironment_q(d1)
         && (_module.ClEnv.ClEnvironment_q(d0) && _module.ClEnv.ClEnvironment_q(d1)
           ==> Map#Equal(_module.ClEnv.m(d0), _module.ClEnv.m(d1)))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.ClEnv($LS(ly), d0, d1) } 
  $Eq#_module.ClEnv($LS(ly), d0, d1) <==> $Eq#_module.ClEnv(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.ClEnv($LS(ly), d0, d1) } 
  $Eq#_module.ClEnv($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.ClEnv(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.ClEnv()) && $Is(d1, Tclass._module.ClEnv())
     ==> ($PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> _module.ClEnv.ClEnvironment_q(d0)
             && _module.ClEnv.ClEnvironment_q(d1)
             && (_module.ClEnv.ClEnvironment_q(d0) && _module.ClEnv.ClEnvironment_q(d1)
               ==> Map#Equal(_module.ClEnv.m(d0), _module.ClEnv.m(d1))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.ClEnv(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.ClEnv(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.ClEnv($LS(ly), d0, d1) } 
  $Eq#_module.ClEnv($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.ClEnv($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.ClEnv(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.ClEnv(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.ClEnv($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1), $PrefixEq#_module.ClEnv(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.ClEnv(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.ClEnv(k, $LS(ly), d0, d1));

const unique class._module.ClEnv: ClassName;

// Constructor function declaration
function #_module.Capsule.Cap(DatatypeType, Map Box Box) : DatatypeType;

const unique ##_module.Capsule.Cap: DtCtorId;

// Constructor identifier
axiom (forall a#85#0#0: DatatypeType, a#85#1#0: Map Box Box :: 
  { #_module.Capsule.Cap(a#85#0#0, a#85#1#0) } 
  DatatypeCtorId(#_module.Capsule.Cap(a#85#0#0, a#85#1#0))
     == ##_module.Capsule.Cap);

function _module.Capsule.Cap_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Capsule.Cap_q(d) } 
  _module.Capsule.Cap_q(d) <==> DatatypeCtorId(d) == ##_module.Capsule.Cap);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Capsule.Cap_q(d) } 
  _module.Capsule.Cap_q(d)
     ==> (exists a#86#0#0: DatatypeType, a#86#1#0: Map Box Box :: 
      d == #_module.Capsule.Cap(a#86#0#0, a#86#1#0)));

function Tclass._module.ConstOrAbs() : Ty;

const unique Tagclass._module.ConstOrAbs: TyTag;

// Tclass._module.ConstOrAbs Tag
axiom Tag(Tclass._module.ConstOrAbs()) == Tagclass._module.ConstOrAbs
   && TagFamily(Tclass._module.ConstOrAbs()) == tytagFamily$ConstOrAbs;

// Box/unbox axiom for Tclass._module.ConstOrAbs
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ConstOrAbs()) } 
  $IsBox(bx, Tclass._module.ConstOrAbs())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.ConstOrAbs()));

function Tclass._module.Capsule() : Ty;

const unique Tagclass._module.Capsule: TyTag;

// Tclass._module.Capsule Tag
axiom Tag(Tclass._module.Capsule()) == Tagclass._module.Capsule
   && TagFamily(Tclass._module.Capsule()) == tytagFamily$Capsule;

// Box/unbox axiom for Tclass._module.Capsule
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Capsule()) } 
  $IsBox(bx, Tclass._module.Capsule())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Capsule()));

// Constructor $Is
axiom (forall a#87#0#0: DatatypeType, a#87#1#0: Map Box Box :: 
  { $Is(#_module.Capsule.Cap(a#87#0#0, a#87#1#0), Tclass._module.Capsule()) } 
  $Is(#_module.Capsule.Cap(a#87#0#0, a#87#1#0), Tclass._module.Capsule())
     <==> $Is(a#87#0#0, Tclass._module.Term())
       && $Is(a#87#1#0, TMap(#$Var, Tclass._module.ConstOrAbs())));

// Constructor $IsAlloc
axiom (forall a#88#0#0: DatatypeType, a#88#1#0: Map Box Box, $h: Heap :: 
  { $IsAlloc(#_module.Capsule.Cap(a#88#0#0, a#88#1#0), Tclass._module.Capsule(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Capsule.Cap(a#88#0#0, a#88#1#0), Tclass._module.Capsule(), $h)
       <==> $IsAlloc(a#88#0#0, Tclass._module.Term(), $h)
         && $IsAlloc(a#88#1#0, TMap(#$Var, Tclass._module.ConstOrAbs()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Capsule.e(d), Tclass._module.Term(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Capsule.Cap_q(d)
       && $IsAlloc(d, Tclass._module.Capsule(), $h)
     ==> $IsAlloc(_module.Capsule.e(d), Tclass._module.Term(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Capsule.s(d), TMap(#$Var, Tclass._module.ConstOrAbs()), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Capsule.Cap_q(d)
       && $IsAlloc(d, Tclass._module.Capsule(), $h)
     ==> $IsAlloc(_module.Capsule.s(d), TMap(#$Var, Tclass._module.ConstOrAbs()), $h));

// Constructor literal
axiom (forall a#89#0#0: DatatypeType, a#89#1#0: Map Box Box :: 
  { #_module.Capsule.Cap(Lit(a#89#0#0), Lit(a#89#1#0)) } 
  #_module.Capsule.Cap(Lit(a#89#0#0), Lit(a#89#1#0))
     == Lit(#_module.Capsule.Cap(a#89#0#0, a#89#1#0)));

function _module.Capsule.e(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#90#0#0: DatatypeType, a#90#1#0: Map Box Box :: 
  { #_module.Capsule.Cap(a#90#0#0, a#90#1#0) } 
  _module.Capsule.e(#_module.Capsule.Cap(a#90#0#0, a#90#1#0)) == a#90#0#0);

// Inductive rank
axiom (forall a#91#0#0: DatatypeType, a#91#1#0: Map Box Box :: 
  { #_module.Capsule.Cap(a#91#0#0, a#91#1#0) } 
  DtRank(a#91#0#0) < DtRank(#_module.Capsule.Cap(a#91#0#0, a#91#1#0)));

function _module.Capsule.s(DatatypeType) : Map Box Box;

// Constructor injectivity
axiom (forall a#92#0#0: DatatypeType, a#92#1#0: Map Box Box :: 
  { #_module.Capsule.Cap(a#92#0#0, a#92#1#0) } 
  _module.Capsule.s(#_module.Capsule.Cap(a#92#0#0, a#92#1#0)) == a#92#1#0);

// Inductive map key rank
axiom (forall a#93#0#0: DatatypeType, a#93#1#0: Map Box Box, d: DatatypeType :: 
  { Map#Domain(a#93#1#0)[$Box(d)], #_module.Capsule.Cap(a#93#0#0, a#93#1#0) } 
  Map#Domain(a#93#1#0)[$Box(d)]
     ==> DtRank(d) < DtRank(#_module.Capsule.Cap(a#93#0#0, a#93#1#0)));

// Inductive map value rank
axiom (forall a#94#0#0: DatatypeType, a#94#1#0: Map Box Box, bx: Box :: 
  { Map#Domain(a#94#1#0)[bx], #_module.Capsule.Cap(a#94#0#0, a#94#1#0) } 
  Map#Domain(a#94#1#0)[bx]
     ==> DtRank($Unbox(Map#Elements(a#94#1#0)[bx]): DatatypeType)
       < DtRank(#_module.Capsule.Cap(a#94#0#0, a#94#1#0)));

// Depth-one case-split function
function $IsA#_module.Capsule(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Capsule(d) } 
  $IsA#_module.Capsule(d) ==> _module.Capsule.Cap_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Capsule.Cap_q(d), $Is(d, Tclass._module.Capsule()) } 
  $Is(d, Tclass._module.Capsule()) ==> _module.Capsule.Cap_q(d));

// Datatype extensional equality declaration
function _module.Capsule#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Capsule.Cap
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Capsule#Equal(a, b) } 
  true
     ==> (_module.Capsule#Equal(a, b)
       <==> _module.Term#Equal(_module.Capsule.e(a), _module.Capsule.e(b))
         && Map#Equal(_module.Capsule.s(a), _module.Capsule.s(b))));

// Datatype extensionality axiom: _module.Capsule
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Capsule#Equal(a, b) } 
  _module.Capsule#Equal(a, b) <==> a == b);

const unique class._module.Capsule: ClassName;

// Constructor function declaration
function #_module.ConstOrAbs.CC(Box) : DatatypeType;

const unique ##_module.ConstOrAbs.CC: DtCtorId;

// Constructor identifier
axiom (forall a#95#0#0: Box :: 
  { #_module.ConstOrAbs.CC(a#95#0#0) } 
  DatatypeCtorId(#_module.ConstOrAbs.CC(a#95#0#0)) == ##_module.ConstOrAbs.CC);

function _module.ConstOrAbs.CC_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.ConstOrAbs.CC_q(d) } 
  _module.ConstOrAbs.CC_q(d) <==> DatatypeCtorId(d) == ##_module.ConstOrAbs.CC);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.ConstOrAbs.CC_q(d) } 
  _module.ConstOrAbs.CC_q(d)
     ==> (exists a#96#0#0: Box :: d == #_module.ConstOrAbs.CC(a#96#0#0)));

// Constructor $Is
axiom (forall a#97#0#0: Box :: 
  { $Is(#_module.ConstOrAbs.CC(a#97#0#0), Tclass._module.ConstOrAbs()) } 
  $Is(#_module.ConstOrAbs.CC(a#97#0#0), Tclass._module.ConstOrAbs())
     <==> $IsBox(a#97#0#0, #$Const));

// Constructor $IsAlloc
axiom (forall a#98#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.ConstOrAbs.CC(a#98#0#0), Tclass._module.ConstOrAbs(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.ConstOrAbs.CC(a#98#0#0), Tclass._module.ConstOrAbs(), $h)
       <==> $IsAllocBox(a#98#0#0, #$Const, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAllocBox(_module.ConstOrAbs.c(d), #$Const, $h) } 
  $IsGoodHeap($h)
       && 
      _module.ConstOrAbs.CC_q(d)
       && $IsAlloc(d, Tclass._module.ConstOrAbs(), $h)
     ==> $IsAllocBox(_module.ConstOrAbs.c(d), #$Const, $h));

// Constructor literal
axiom (forall a#99#0#0: Box :: 
  { #_module.ConstOrAbs.CC(Lit(a#99#0#0)) } 
  #_module.ConstOrAbs.CC(Lit(a#99#0#0)) == Lit(#_module.ConstOrAbs.CC(a#99#0#0)));

function _module.ConstOrAbs.c(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#100#0#0: Box :: 
  { #_module.ConstOrAbs.CC(a#100#0#0) } 
  _module.ConstOrAbs.c(#_module.ConstOrAbs.CC(a#100#0#0)) == a#100#0#0);

// Inductive rank
axiom (forall a#101#0#0: Box :: 
  { #_module.ConstOrAbs.CC(a#101#0#0) } 
  BoxRank(a#101#0#0) < DtRank(#_module.ConstOrAbs.CC(a#101#0#0)));

// Constructor function declaration
function #_module.ConstOrAbs.AA(DatatypeType) : DatatypeType;

const unique ##_module.ConstOrAbs.AA: DtCtorId;

// Constructor identifier
axiom (forall a#102#0#0: DatatypeType :: 
  { #_module.ConstOrAbs.AA(a#102#0#0) } 
  DatatypeCtorId(#_module.ConstOrAbs.AA(a#102#0#0)) == ##_module.ConstOrAbs.AA);

function _module.ConstOrAbs.AA_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.ConstOrAbs.AA_q(d) } 
  _module.ConstOrAbs.AA_q(d) <==> DatatypeCtorId(d) == ##_module.ConstOrAbs.AA);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.ConstOrAbs.AA_q(d) } 
  _module.ConstOrAbs.AA_q(d)
     ==> (exists a#103#0#0: DatatypeType :: d == #_module.ConstOrAbs.AA(a#103#0#0)));

// Constructor $Is
axiom (forall a#104#0#0: DatatypeType :: 
  { $Is(#_module.ConstOrAbs.AA(a#104#0#0), Tclass._module.ConstOrAbs()) } 
  $Is(#_module.ConstOrAbs.AA(a#104#0#0), Tclass._module.ConstOrAbs())
     <==> $Is(a#104#0#0, Tclass._module.LambdaAbs()));

// Constructor $IsAlloc
axiom (forall a#105#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.ConstOrAbs.AA(a#105#0#0), Tclass._module.ConstOrAbs(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.ConstOrAbs.AA(a#105#0#0), Tclass._module.ConstOrAbs(), $h)
       <==> $IsAlloc(a#105#0#0, Tclass._module.LambdaAbs(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.ConstOrAbs.abs(d), Tclass._module.LambdaAbs(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.ConstOrAbs.AA_q(d)
       && $IsAlloc(d, Tclass._module.ConstOrAbs(), $h)
     ==> $IsAlloc(_module.ConstOrAbs.abs(d), Tclass._module.LambdaAbs(), $h));

// Constructor literal
axiom (forall a#106#0#0: DatatypeType :: 
  { #_module.ConstOrAbs.AA(Lit(a#106#0#0)) } 
  #_module.ConstOrAbs.AA(Lit(a#106#0#0)) == Lit(#_module.ConstOrAbs.AA(a#106#0#0)));

function _module.ConstOrAbs.abs(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#107#0#0: DatatypeType :: 
  { #_module.ConstOrAbs.AA(a#107#0#0) } 
  _module.ConstOrAbs.abs(#_module.ConstOrAbs.AA(a#107#0#0)) == a#107#0#0);

// Inductive rank
axiom (forall a#108#0#0: DatatypeType :: 
  { #_module.ConstOrAbs.AA(a#108#0#0) } 
  DtRank(a#108#0#0) < DtRank(#_module.ConstOrAbs.AA(a#108#0#0)));

// Depth-one case-split function
function $IsA#_module.ConstOrAbs(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.ConstOrAbs(d) } 
  $IsA#_module.ConstOrAbs(d)
     ==> _module.ConstOrAbs.CC_q(d) || _module.ConstOrAbs.AA_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.ConstOrAbs.AA_q(d), $Is(d, Tclass._module.ConstOrAbs()) } 
    { _module.ConstOrAbs.CC_q(d), $Is(d, Tclass._module.ConstOrAbs()) } 
  $Is(d, Tclass._module.ConstOrAbs())
     ==> _module.ConstOrAbs.CC_q(d) || _module.ConstOrAbs.AA_q(d));

// Datatype extensional equality declaration
function _module.ConstOrAbs#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.ConstOrAbs.CC
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.ConstOrAbs#Equal(a, b), _module.ConstOrAbs.CC_q(a) } 
    { _module.ConstOrAbs#Equal(a, b), _module.ConstOrAbs.CC_q(b) } 
  _module.ConstOrAbs.CC_q(a) && _module.ConstOrAbs.CC_q(b)
     ==> (_module.ConstOrAbs#Equal(a, b)
       <==> _module.ConstOrAbs.c(a) == _module.ConstOrAbs.c(b)));

// Datatype extensional equality definition: #_module.ConstOrAbs.AA
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.ConstOrAbs#Equal(a, b), _module.ConstOrAbs.AA_q(a) } 
    { _module.ConstOrAbs#Equal(a, b), _module.ConstOrAbs.AA_q(b) } 
  _module.ConstOrAbs.AA_q(a) && _module.ConstOrAbs.AA_q(b)
     ==> (_module.ConstOrAbs#Equal(a, b)
       <==> _module.LambdaAbs#Equal(_module.ConstOrAbs.abs(a), _module.ConstOrAbs.abs(b))));

// Datatype extensionality axiom: _module.ConstOrAbs
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.ConstOrAbs#Equal(a, b) } 
  _module.ConstOrAbs#Equal(a, b) <==> a == b);

const unique class._module.ConstOrAbs: ClassName;

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

// function declaration for _module._default.LexLess
function _module.__default.LexLess($ly: LayerType, s#0: DatatypeType, t#0: DatatypeType) : bool;

function _module.__default.LexLess#canCall(s#0: DatatypeType, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.LexLess($LS($ly), s#0, t#0) } 
  _module.__default.LexLess($LS($ly), s#0, t#0)
     == _module.__default.LexLess($ly, s#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.LexLess(AsFuelBottom($ly), s#0, t#0) } 
  _module.__default.LexLess($ly, s#0, t#0)
     == _module.__default.LexLess($LZ, s#0, t#0));

// consequence axiom for _module.__default.LexLess
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.LexLess($ly, s#0, t#0) } 
    _module.__default.LexLess#canCall(s#0, t#0)
         || (1 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.LexLess#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.LexLess
axiom (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.LexLess#requires($ly, s#0, t#0) } 
  $Is(s#0, Tclass._module.Stream(TInt)) && $Is(t#0, Tclass._module.Stream(TInt))
     ==> _module.__default.LexLess#requires($ly, s#0, t#0) == true);

// definition axiom for _module.__default.LexLess (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.LexLess($LS($ly), s#0, t#0) } 
    _module.__default.LexLess#canCall(s#0, t#0)
         || (1 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> _module.Stream.Cons_q(s#0)
         && _module.Stream.Cons_q(t#0)
         && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && _module.__default.LexLess#canCall(_module.Stream.tl(s#0), _module.Stream.tl(t#0))))
         && _module.__default.LexLess($LS($ly), s#0, t#0)
           == ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
             && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.__default.LexLess($ly, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))));

// 1st prefix predicate axiom for _module.__default.LexLess_h
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.LexLess($LS($ly), s#0, t#0) } 
    $Is(s#0, Tclass._module.Stream(TInt))
         && $Is(t#0, Tclass._module.Stream(TInt))
         && _module.__default.LexLess($LS($ly), s#0, t#0)
       ==> (forall _k#0: int :: 
        { _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0) } 
        LitInt(0) <= _k#0 ==> _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0)));

// 2nd prefix predicate axiom
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.LexLess($LS($ly), s#0, t#0) } 
    $Is(s#0, Tclass._module.Stream(TInt))
         && $Is(t#0, Tclass._module.Stream(TInt))
         && (forall _k#0: int :: 
          { _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0) } 
          LitInt(0) <= _k#0 ==> _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0))
       ==> _module.__default.LexLess($LS($ly), s#0, t#0));

// 3rd prefix predicate axiom
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType, _k#0: int :: 
    { _module.__default.LexLess_h($ly, _k#0, s#0, t#0) } 
    $Is(s#0, Tclass._module.Stream(TInt))
         && $Is(t#0, Tclass._module.Stream(TInt))
         && _k#0 == 0
       ==> _module.__default.LexLess_h($ly, _k#0, s#0, t#0));

procedure CheckWellformed$$_module.__default.LexLess(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(TInt)), 
    t#0: DatatypeType where $Is(t#0, Tclass._module.Stream(TInt)));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.LexLess(s#0: DatatypeType, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##t#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function LexLess
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(20,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(t#0);
        if ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int)
        {
            assume _module.Stream.Cons_q(s#0);
            assume _module.Stream.Cons_q(t#0);
            if ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int)
            {
                assume _module.Stream.Cons_q(s#0);
                assume _module.Stream.Cons_q(t#0);
                ##s#0 := _module.Stream.tl(s#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
                ##t#0 := _module.Stream.tl(t#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0, Tclass._module.Stream(TInt), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.LexLess#canCall(_module.Stream.tl(s#0), _module.Stream.tl(t#0));
            }
        }

        assume _module.__default.LexLess($LS($LZ), s#0, t#0)
           == ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
             && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(t#0))));
        assume _module.Stream.Cons_q(s#0)
           && _module.Stream.Cons_q(t#0)
           && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
             ==> _module.Stream.Cons_q(s#0)
               && _module.Stream.Cons_q(t#0)
               && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                 ==> _module.Stream.Cons_q(s#0)
                   && _module.Stream.Cons_q(t#0)
                   && _module.__default.LexLess#canCall(_module.Stream.tl(s#0), _module.Stream.tl(t#0))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.LexLess($LS($LZ), s#0, t#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.LexLess#
function _module.__default.LexLess_h($ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType) : bool;

function _module.__default.LexLess_h#canCall(_k#0: int, s#0: DatatypeType, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0) } 
  _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0)
     == _module.__default.LexLess_h($ly, _k#0, s#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.LexLess_h(AsFuelBottom($ly), _k#0, s#0, t#0) } 
  _module.__default.LexLess_h($ly, _k#0, s#0, t#0)
     == _module.__default.LexLess_h($LZ, _k#0, s#0, t#0));

// consequence axiom for _module.__default.LexLess_h
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.LexLess_h($ly, _k#0, s#0, t#0) } 
    _module.__default.LexLess_h#canCall(_k#0, s#0, t#0)
         || (3 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.LexLess_h#requires(LayerType, int, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.LexLess_h
axiom (forall $ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.LexLess_h#requires($ly, _k#0, s#0, t#0) } 
  LitInt(0) <= _k#0
       && $Is(s#0, Tclass._module.Stream(TInt))
       && $Is(t#0, Tclass._module.Stream(TInt))
     ==> _module.__default.LexLess_h#requires($ly, _k#0, s#0, t#0) == true);

// definition axiom for _module.__default.LexLess_h (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0) } 
    _module.__default.LexLess_h#canCall(_k#0, s#0, t#0)
         || (3 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                   ==> _module.Stream.Cons_q(s#0)
                     && _module.Stream.Cons_q(t#0)
                     && _module.__default.LexLess_h#canCall(_k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))))
         && _module.__default.LexLess_h($LS($ly), _k#0, s#0, t#0)
           == (0 < _k#0
             ==> $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                 ==> _module.__default.LexLess_h($ly, _k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))));

// definition axiom for _module.__default.LexLess_h for decreasing-related literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    {:weight 3} { _module.__default.LexLess_h($LS($ly), LitInt(_k#0), s#0, t#0) } 
    _module.__default.LexLess_h#canCall(LitInt(_k#0), s#0, t#0)
         || (3 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                   ==> _module.Stream.Cons_q(s#0)
                     && _module.Stream.Cons_q(t#0)
                     && _module.__default.LexLess_h#canCall(_k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))))
         && _module.__default.LexLess_h($LS($ly), LitInt(_k#0), s#0, t#0)
           == (0 < _k#0
             ==> $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                 ==> _module.__default.LexLess_h($LS($ly), _k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))));

// definition axiom for _module.__default.LexLess_h for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    {:weight 3} { _module.__default.LexLess_h($LS($ly), LitInt(_k#0), Lit(s#0), Lit(t#0)) } 
    _module.__default.LexLess_h#canCall(LitInt(_k#0), Lit(s#0), Lit(t#0))
         || (3 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                   ==> _module.Stream.Cons_q(s#0)
                     && _module.Stream.Cons_q(t#0)
                     && _module.__default.LexLess_h#canCall(_k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))))
         && _module.__default.LexLess_h($LS($ly), LitInt(_k#0), Lit(s#0), Lit(t#0))
           == (0 < _k#0
             ==> $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                 ==> _module.__default.LexLess_h($LS($ly), _k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))));

procedure CheckWellformed$$_module.__default.Theorem1__LexLess__Is__Transitive(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem1__LexLess__Is__Transitive(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int;
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  requires _module.__default.LexLess#canCall(t#0, u#0)
     ==> _module.__default.LexLess($LS($LZ), t#0, u#0)
       || $Unbox(_module.Stream.hd(t#0)): int <= $Unbox(_module.Stream.hd(u#0)): int;
  requires _module.__default.LexLess#canCall(t#0, u#0)
     ==> _module.__default.LexLess($LS($LZ), t#0, u#0)
       || ($Unbox(_module.Stream.hd(t#0)): int == $Unbox(_module.Stream.hd(u#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(t#0), _module.Stream.tl(u#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess#canCall(s#0, u#0);
  free ensures _module.__default.LexLess#canCall(s#0, u#0)
     && 
    _module.__default.LexLess($LS($LZ), s#0, u#0)
     && 
    $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(u#0)): int
     && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(u#0)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(u#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1, u#1} CoCall$$_module.__default.Theorem1__LexLess__Is__Transitive_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(TInt))
         && $IsAlloc(u#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#1));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#1, t#1)
     ==> _module.__default.LexLess($LS($LZ), s#1, t#1)
       || $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int;
  requires _module.__default.LexLess#canCall(s#1, t#1)
     ==> _module.__default.LexLess($LS($LZ), s#1, t#1)
       || ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#1), _module.Stream.tl(t#1)));
  requires _module.__default.LexLess#canCall(t#1, u#1)
     ==> _module.__default.LexLess($LS($LZ), t#1, u#1)
       || $Unbox(_module.Stream.hd(t#1)): int <= $Unbox(_module.Stream.hd(u#1)): int;
  requires _module.__default.LexLess#canCall(t#1, u#1)
     ==> _module.__default.LexLess($LS($LZ), t#1, u#1)
       || ($Unbox(_module.Stream.hd(t#1)): int == $Unbox(_module.Stream.hd(u#1)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(t#1), _module.Stream.tl(u#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1);
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1)
     && 
    _module.__default.LexLess_h($LS($LZ), _k#0, s#1, u#1)
     && (0 < _k#0
       ==> $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(u#1)): int
         && ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(u#1)): int
           ==> _module.__default.LexLess_h($LS($LZ), _k#0 - 1, _module.Stream.tl(s#1), _module.Stream.tl(u#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1, u#1} Impl$$_module.__default.Theorem1__LexLess__Is__Transitive_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(TInt))
         && $IsAlloc(u#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#1))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.LexLess#canCall(s#1, t#1)
     && 
    _module.__default.LexLess($LS($LZ), s#1, t#1)
     && 
    $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int
     && ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#1), _module.Stream.tl(t#1)));
  free requires _module.__default.LexLess#canCall(t#1, u#1)
     && 
    _module.__default.LexLess($LS($LZ), t#1, u#1)
     && 
    $Unbox(_module.Stream.hd(t#1)): int <= $Unbox(_module.Stream.hd(u#1)): int
     && ($Unbox(_module.Stream.hd(t#1)): int == $Unbox(_module.Stream.hd(u#1)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(t#1), _module.Stream.tl(u#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1);
  ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1)
     ==> _module.__default.LexLess_h($LS($LZ), _k#0, s#1, u#1)
       || (0 < _k#0
         ==> $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(u#1)): int);
  ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1)
     ==> _module.__default.LexLess_h($LS($LZ), _k#0, s#1, u#1)
       || (0 < _k#0
         ==> 
        $Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(u#1)): int
         ==> _module.__default.LexLess_h($LS($LS($LZ)), _k#0 - 1, _module.Stream.tl(s#1), _module.Stream.tl(u#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, t#1, u#1} Impl$$_module.__default.Theorem1__LexLess__Is__Transitive_h(_k#0: int, s#1: DatatypeType, t#1: DatatypeType, u#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: int;
  var s##0: DatatypeType;
  var t##0: DatatypeType;
  var u##0: DatatypeType;

    // AddMethodImpl: Theorem1_LexLess_Is_Transitive#, Impl$$_module.__default.Theorem1__LexLess__Is__Transitive_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(27,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(t#1);
    assume $IsA#_module.Stream(u#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, 
        $ih#s0#0: DatatypeType, 
        $ih#t0#0: DatatypeType, 
        $ih#u0#0: DatatypeType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && $Is($ih#u0#0, Tclass._module.Stream(TInt))
           && 
          _module.__default.LexLess($LS($LZ), $ih#s0#0, $ih#t0#0)
           && _module.__default.LexLess($LS($LZ), $ih#t0#0, $ih#u0#0)
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.LexLess_h($LS($LZ), $ih#_k0#0, $ih#s0#0, $ih#u0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(30,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(36,3)
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(u#1);
        assume _module.Stream.Cons_q(s#1) && _module.Stream.Cons_q(u#1);
        if ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(u#1)): int)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(37,35)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(_k#0 - 1, Tclass._System.nat());
            _k##0 := _k#0 - 1;
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            s##0 := _module.Stream.tl(s#1);
            assume _module.Stream.Cons_q(t#1);
            assume _module.Stream.Cons_q(t#1);
            // ProcessCallStmt: CheckSubrange
            t##0 := _module.Stream.tl(t#1);
            assume _module.Stream.Cons_q(u#1);
            assume _module.Stream.Cons_q(u#1);
            // ProcessCallStmt: CheckSubrange
            u##0 := _module.Stream.tl(u#1);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem1__LexLess__Is__Transitive_h(_k##0, s##0, t##0, u##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(37,52)"} true;
        }
        else
        {
        }
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.Theorem1__LexLess__Is__Transitive__Automatic(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem1__LexLess__Is__Transitive__Automatic(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int;
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  requires _module.__default.LexLess#canCall(t#0, u#0)
     ==> _module.__default.LexLess($LS($LZ), t#0, u#0)
       || $Unbox(_module.Stream.hd(t#0)): int <= $Unbox(_module.Stream.hd(u#0)): int;
  requires _module.__default.LexLess#canCall(t#0, u#0)
     ==> _module.__default.LexLess($LS($LZ), t#0, u#0)
       || ($Unbox(_module.Stream.hd(t#0)): int == $Unbox(_module.Stream.hd(u#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(t#0), _module.Stream.tl(u#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess#canCall(s#0, u#0);
  free ensures _module.__default.LexLess#canCall(s#0, u#0)
     && 
    _module.__default.LexLess($LS($LZ), s#0, u#0)
     && 
    $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(u#0)): int
     && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(u#0)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(u#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1, u#1} CoCall$$_module.__default.Theorem1__LexLess__Is__Transitive__Automatic_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(TInt))
         && $IsAlloc(u#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#1));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#1, t#1)
     ==> _module.__default.LexLess($LS($LZ), s#1, t#1)
       || $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int;
  requires _module.__default.LexLess#canCall(s#1, t#1)
     ==> _module.__default.LexLess($LS($LZ), s#1, t#1)
       || ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#1), _module.Stream.tl(t#1)));
  requires _module.__default.LexLess#canCall(t#1, u#1)
     ==> _module.__default.LexLess($LS($LZ), t#1, u#1)
       || $Unbox(_module.Stream.hd(t#1)): int <= $Unbox(_module.Stream.hd(u#1)): int;
  requires _module.__default.LexLess#canCall(t#1, u#1)
     ==> _module.__default.LexLess($LS($LZ), t#1, u#1)
       || ($Unbox(_module.Stream.hd(t#1)): int == $Unbox(_module.Stream.hd(u#1)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(t#1), _module.Stream.tl(u#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1);
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1)
     && 
    _module.__default.LexLess_h($LS($LZ), _k#0, s#1, u#1)
     && (0 < _k#0
       ==> $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(u#1)): int
         && ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(u#1)): int
           ==> _module.__default.LexLess_h($LS($LZ), _k#0 - 1, _module.Stream.tl(s#1), _module.Stream.tl(u#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1, u#1} Impl$$_module.__default.Theorem1__LexLess__Is__Transitive__Automatic_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(TInt))
         && $IsAlloc(u#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#1))
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.LexLess#canCall(s#1, t#1)
     && 
    _module.__default.LexLess($LS($LZ), s#1, t#1)
     && 
    $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int
     && ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#1), _module.Stream.tl(t#1)));
  free requires _module.__default.LexLess#canCall(t#1, u#1)
     && 
    _module.__default.LexLess($LS($LZ), t#1, u#1)
     && 
    $Unbox(_module.Stream.hd(t#1)): int <= $Unbox(_module.Stream.hd(u#1)): int
     && ($Unbox(_module.Stream.hd(t#1)): int == $Unbox(_module.Stream.hd(u#1)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(t#1), _module.Stream.tl(u#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1);
  ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1)
     ==> _module.__default.LexLess_h($LS($LZ), _k#0, s#1, u#1)
       || (0 < _k#0
         ==> $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(u#1)): int);
  ensures _module.__default.LexLess_h#canCall(_k#0, s#1, u#1)
     ==> _module.__default.LexLess_h($LS($LZ), _k#0, s#1, u#1)
       || (0 < _k#0
         ==> 
        $Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(u#1)): int
         ==> _module.__default.LexLess_h($LS($LS($LZ)), _k#0 - 1, _module.Stream.tl(s#1), _module.Stream.tl(u#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, t#1, u#1} Impl$$_module.__default.Theorem1__LexLess__Is__Transitive__Automatic_h(_k#0: int, s#1: DatatypeType, t#1: DatatypeType, u#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem1_LexLess_Is_Transitive_Automatic#, Impl$$_module.__default.Theorem1__LexLess__Is__Transitive__Automatic_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(42,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(t#1);
    assume $IsA#_module.Stream(u#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, 
        $ih#s0#0: DatatypeType, 
        $ih#t0#0: DatatypeType, 
        $ih#u0#0: DatatypeType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && $Is($ih#u0#0, Tclass._module.Stream(TInt))
           && 
          _module.__default.LexLess($LS($LZ), $ih#s0#0, $ih#t0#0)
           && _module.__default.LexLess($LS($LZ), $ih#t0#0, $ih#u0#0)
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.LexLess_h($LS($LZ), $ih#_k0#0, $ih#s0#0, $ih#u0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(45,1)
    assume true;
    if (0 < _k#0)
    {
    }
    else
    {
    }
}



// function declaration for _module._default.NotLexLess
function _module.__default.NotLexLess(s#0: DatatypeType, t#0: DatatypeType) : bool;

function _module.__default.NotLexLess#canCall(s#0: DatatypeType, t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.NotLexLess
axiom 9 <= $FunctionContextHeight
   ==> (forall s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.NotLexLess(s#0, t#0) } 
    _module.__default.NotLexLess#canCall(s#0, t#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.NotLexLess#requires(DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.NotLexLess
axiom (forall s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.NotLexLess#requires(s#0, t#0) } 
  $Is(s#0, Tclass._module.Stream(TInt)) && $Is(t#0, Tclass._module.Stream(TInt))
     ==> _module.__default.NotLexLess#requires(s#0, t#0) == true);

// definition axiom for _module.__default.NotLexLess (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.NotLexLess(s#0, t#0) } 
    _module.__default.NotLexLess#canCall(s#0, t#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (forall k#0: int :: 
          { _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0) } 
          LitInt(0) <= k#0 ==> _module.__default.NotLexLess_k#canCall(k#0, s#0, t#0))
         && _module.__default.NotLexLess(s#0, t#0)
           == (exists k#0: int :: 
            { _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0) } 
            LitInt(0) <= k#0 && _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0)));

// definition axiom for _module.__default.NotLexLess for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall s#0: DatatypeType, t#0: DatatypeType :: 
    {:weight 3} { _module.__default.NotLexLess(Lit(s#0), Lit(t#0)) } 
    _module.__default.NotLexLess#canCall(Lit(s#0), Lit(t#0))
         || (9 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (forall k#1: int :: 
          { _module.__default.NotLexLess_k($LS($LZ), k#1, s#0, t#0) } 
          LitInt(0) <= k#1
             ==> _module.__default.NotLexLess_k#canCall(k#1, Lit(s#0), Lit(t#0)))
         && _module.__default.NotLexLess(Lit(s#0), Lit(t#0))
           == (exists k#1: int :: 
            { _module.__default.NotLexLess_k($LS($LZ), k#1, s#0, t#0) } 
            LitInt(0) <= k#1
               && _module.__default.NotLexLess_k($LS($LZ), k#1, Lit(s#0), Lit(t#0))));

procedure CheckWellformed$$_module.__default.NotLexLess(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(TInt)), 
    t#0: DatatypeType where $Is(t#0, Tclass._module.Stream(TInt)));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.NotLexLess(s#0: DatatypeType, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#2: int;
  var ##k#0: int;
  var ##s#0: DatatypeType;
  var ##t#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function NotLexLess
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(51,10): initial state"} true;
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
        havoc k#2;
        if (LitInt(0) <= k#2)
        {
            ##k#0 := k#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##k#0, Tclass._System.nat(), $Heap);
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Stream(TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.NotLexLess_k#canCall(k#2, s#0, t#0);
        }

        // End Comprehension WF check
        assume _module.__default.NotLexLess(s#0, t#0)
           == (exists k#3: int :: 
            { _module.__default.NotLexLess_k($LS($LZ), k#3, s#0, t#0) } 
            LitInt(0) <= k#3 && _module.__default.NotLexLess_k($LS($LZ), k#3, s#0, t#0));
        assume (forall k#3: int :: 
          { _module.__default.NotLexLess_k($LS($LZ), k#3, s#0, t#0) } 
          LitInt(0) <= k#3 ==> _module.__default.NotLexLess_k#canCall(k#3, s#0, t#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.NotLexLess(s#0, t#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.NotLexLess'
function _module.__default.NotLexLess_k($ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType) : bool;

function _module.__default.NotLexLess_k#canCall(k#0: int, s#0: DatatypeType, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.NotLexLess_k($LS($ly), k#0, s#0, t#0) } 
  _module.__default.NotLexLess_k($LS($ly), k#0, s#0, t#0)
     == _module.__default.NotLexLess_k($ly, k#0, s#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.NotLexLess_k(AsFuelBottom($ly), k#0, s#0, t#0) } 
  _module.__default.NotLexLess_k($ly, k#0, s#0, t#0)
     == _module.__default.NotLexLess_k($LZ, k#0, s#0, t#0));

// consequence axiom for _module.__default.NotLexLess_k
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.NotLexLess_k($ly, k#0, s#0, t#0) } 
    _module.__default.NotLexLess_k#canCall(k#0, s#0, t#0)
         || (8 != $FunctionContextHeight
           && 
          LitInt(0) <= k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.NotLexLess_k#requires(LayerType, int, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.NotLexLess_k
axiom (forall $ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.NotLexLess_k#requires($ly, k#0, s#0, t#0) } 
  LitInt(0) <= k#0
       && $Is(s#0, Tclass._module.Stream(TInt))
       && $Is(t#0, Tclass._module.Stream(TInt))
     ==> _module.__default.NotLexLess_k#requires($ly, k#0, s#0, t#0) == true);

// definition axiom for _module.__default.NotLexLess_k (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.NotLexLess_k($LS($ly), k#0, s#0, t#0) } 
    _module.__default.NotLexLess_k#canCall(k#0, s#0, t#0)
         || (8 != $FunctionContextHeight
           && 
          LitInt(0) <= k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (k#0 != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                   ==> _module.Stream.Cons_q(s#0)
                     && _module.Stream.Cons_q(t#0)
                     && _module.__default.NotLexLess_k#canCall(k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))))
         && _module.__default.NotLexLess_k($LS($ly), k#0, s#0, t#0)
           == (if k#0 == LitInt(0)
             then false
             else !($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int)
               || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                 && _module.__default.NotLexLess_k($ly, k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))));

// definition axiom for _module.__default.NotLexLess_k for decreasing-related literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    {:weight 3} { _module.__default.NotLexLess_k($LS($ly), LitInt(k#0), s#0, t#0) } 
    _module.__default.NotLexLess_k#canCall(LitInt(k#0), s#0, t#0)
         || (8 != $FunctionContextHeight
           && 
          LitInt(0) <= k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (LitInt(k#0) != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                   ==> _module.Stream.Cons_q(s#0)
                     && _module.Stream.Cons_q(t#0)
                     && _module.__default.NotLexLess_k#canCall(LitInt(k#0 - 1), _module.Stream.tl(s#0), _module.Stream.tl(t#0)))))
         && _module.__default.NotLexLess_k($LS($ly), LitInt(k#0), s#0, t#0)
           == (if LitInt(k#0) == LitInt(0)
             then false
             else !($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int)
               || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                 && _module.__default.NotLexLess_k($LS($ly), LitInt(k#0 - 1), _module.Stream.tl(s#0), _module.Stream.tl(t#0)))));

// definition axiom for _module.__default.NotLexLess_k for all literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, k#0: int, s#0: DatatypeType, t#0: DatatypeType :: 
    {:weight 3} { _module.__default.NotLexLess_k($LS($ly), LitInt(k#0), Lit(s#0), Lit(t#0)) } 
    _module.__default.NotLexLess_k#canCall(LitInt(k#0), Lit(s#0), Lit(t#0))
         || (8 != $FunctionContextHeight
           && 
          LitInt(0) <= k#0
           && $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> (LitInt(k#0) != LitInt(0)
           ==> _module.Stream.Cons_q(Lit(s#0))
             && _module.Stream.Cons_q(Lit(t#0))
             && (LitInt($Unbox(_module.Stream.hd(Lit(s#0))): int)
                 <= LitInt($Unbox(_module.Stream.hd(Lit(t#0))): int)
               ==> _module.Stream.Cons_q(Lit(s#0))
                 && _module.Stream.Cons_q(Lit(t#0))
                 && (LitInt($Unbox(_module.Stream.hd(Lit(s#0))): int)
                     == LitInt($Unbox(_module.Stream.hd(Lit(t#0))): int)
                   ==> _module.Stream.Cons_q(Lit(s#0))
                     && _module.Stream.Cons_q(Lit(t#0))
                     && _module.__default.NotLexLess_k#canCall(LitInt(k#0 - 1), 
                      Lit(_module.Stream.tl(Lit(s#0))), 
                      Lit(_module.Stream.tl(Lit(t#0)))))))
         && _module.__default.NotLexLess_k($LS($ly), LitInt(k#0), Lit(s#0), Lit(t#0))
           == (if LitInt(k#0) == LitInt(0)
             then false
             else !(LitInt($Unbox(_module.Stream.hd(Lit(s#0))): int)
                 <= LitInt($Unbox(_module.Stream.hd(Lit(t#0))): int))
               || (LitInt($Unbox(_module.Stream.hd(Lit(s#0))): int)
                   == LitInt($Unbox(_module.Stream.hd(Lit(t#0))): int)
                 && _module.__default.NotLexLess_k($LS($ly), 
                  LitInt(k#0 - 1), 
                  Lit(_module.Stream.tl(Lit(s#0))), 
                  Lit(_module.Stream.tl(Lit(t#0)))))));

procedure CheckWellformed$$_module.__default.NotLexLess_k(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(TInt)), 
    t#0: DatatypeType where $Is(t#0, Tclass._module.Stream(TInt)));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.NotLexLess_k(k#0: int, s#0: DatatypeType, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##k#0: int;
  var ##s#0: DatatypeType;
  var ##t#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function NotLexLess'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(55,10): initial state"} true;
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
        if (k#0 == LitInt(0))
        {
            assume _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0) == Lit(false);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0), TBool);
        }
        else
        {
            assume _module.Stream.Cons_q(s#0);
            assume _module.Stream.Cons_q(t#0);
            if ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int)
            {
                assume _module.Stream.Cons_q(s#0);
                assume _module.Stream.Cons_q(t#0);
                if ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int)
                {
                    assume _module.Stream.Cons_q(s#0);
                    assume _module.Stream.Cons_q(t#0);
                    assert $Is(k#0 - 1, Tclass._System.nat());
                    ##k#0 := k#0 - 1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##k#0, Tclass._System.nat(), $Heap);
                    ##s#0 := _module.Stream.tl(s#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
                    ##t#0 := _module.Stream.tl(t#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#0, Tclass._module.Stream(TInt), $Heap);
                    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assert 0 <= k#0 || ##k#0 == k#0;
                    assert ##k#0 < k#0;
                    assume _module.__default.NotLexLess_k#canCall(k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0));
                }
            }

            assume _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0)
               == (!($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int)
                 || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                   && _module.__default.NotLexLess_k($LS($LZ), k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0))));
            assume _module.Stream.Cons_q(s#0)
               && _module.Stream.Cons_q(t#0)
               && ($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
                 ==> _module.Stream.Cons_q(s#0)
                   && _module.Stream.Cons_q(t#0)
                   && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
                     ==> _module.Stream.Cons_q(s#0)
                       && _module.Stream.Cons_q(t#0)
                       && _module.__default.NotLexLess_k#canCall(k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0))));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0), TBool);
        }

        assert b$reqreads#0;
    }
}



procedure {:_induction s#0, t#0} CheckWellformed$$_module.__default.EquivalenceTheorem(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, t#0} Call$$_module.__default.EquivalenceTheorem(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess#canCall(s#0, t#0)
     && _module.__default.NotLexLess#canCall(s#0, t#0);
  ensures _module.__default.LexLess($LS($LS($LZ)), s#0, t#0)
     <==> !_module.__default.NotLexLess(s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, t#0} Impl$$_module.__default.EquivalenceTheorem(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0))
   returns ($_reverifyPost: bool);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess#canCall(s#0, t#0)
     && _module.__default.NotLexLess#canCall(s#0, t#0);
  ensures _module.__default.LexLess($LS($LS($LZ)), s#0, t#0)
     <==> !_module.__default.NotLexLess(s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, t#0} Impl$$_module.__default.EquivalenceTheorem(s#0: DatatypeType, t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##s#2: DatatypeType;
  var ##t#2: DatatypeType;
  var s##0_0: DatatypeType;
  var t##0_0: DatatypeType;
  var ##s#3: DatatypeType;
  var ##t#3: DatatypeType;
  var s##1_0: DatatypeType;
  var t##1_0: DatatypeType;

    // AddMethodImpl: EquivalenceTheorem, Impl$$_module.__default.EquivalenceTheorem
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(63,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    assume $IsA#_module.Stream(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#t0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && Lit(true)
           && false
         ==> (_module.__default.LexLess($LS($LZ), $ih#s0#0, $ih#t0#0)
           <==> !_module.__default.NotLexLess($ih#s0#0, $ih#t0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(64,3)
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(TInt), $Heap);
    ##t#2 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#2, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.NotLexLess#canCall(s#0, t#0);
    assume _module.__default.NotLexLess#canCall(s#0, t#0);
    if (!_module.__default.NotLexLess(s#0, t#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(65,24)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0_0 := t#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.EquivalenceTheorem0(s##0_0, t##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(65,29)"} true;
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(67,3)
    ##s#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, Tclass._module.Stream(TInt), $Heap);
    ##t#3 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#3, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.LexLess#canCall(s#0, t#0);
    assume _module.__default.LexLess#canCall(s#0, t#0);
    if (_module.__default.LexLess($LS($LZ), s#0, t#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(68,24)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##1_0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##1_0 := t#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.EquivalenceTheorem1(s##1_0, t##1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(68,29)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.EquivalenceTheorem0(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.EquivalenceTheorem0(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  // user-defined preconditions
  requires !_module.__default.NotLexLess(s#0, t#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess#canCall(s#0, t#0);
  free ensures _module.__default.LexLess#canCall(s#0, t#0)
     && 
    _module.__default.LexLess($LS($LZ), s#0, t#0)
     && 
    $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
     && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1} CoCall$$_module.__default.EquivalenceTheorem0_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1));
  // user-defined preconditions
  requires !_module.__default.NotLexLess(s#1, t#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, t#1);
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, t#1)
     && 
    _module.__default.LexLess_h($LS($LZ), _k#0, s#1, t#1)
     && (0 < _k#0
       ==> $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int
         && ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
           ==> _module.__default.LexLess_h($LS($LZ), _k#0 - 1, _module.Stream.tl(s#1), _module.Stream.tl(t#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1} Impl$$_module.__default.EquivalenceTheorem0_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.__default.NotLexLess(s#1, t#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(_k#0, s#1, t#1);
  ensures _module.__default.LexLess_h#canCall(_k#0, s#1, t#1)
     ==> _module.__default.LexLess_h($LS($LZ), _k#0, s#1, t#1)
       || (0 < _k#0
         ==> $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int);
  ensures _module.__default.LexLess_h#canCall(_k#0, s#1, t#1)
     ==> _module.__default.LexLess_h($LS($LZ), _k#0, s#1, t#1)
       || (0 < _k#0
         ==> 
        $Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
         ==> _module.__default.LexLess_h($LS($LS($LZ)), _k#0 - 1, _module.Stream.tl(s#1), _module.Stream.tl(t#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, t#1} Impl$$_module.__default.EquivalenceTheorem0_h(_k#0: int, s#1: DatatypeType, t#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var k##0: int;
  var s##0: DatatypeType;
  var t##0: DatatypeType;

    // AddMethodImpl: EquivalenceTheorem0#, Impl$$_module.__default.EquivalenceTheorem0_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(71,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(t#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, $ih#s0#0: DatatypeType, $ih#t0#0: DatatypeType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && !_module.__default.NotLexLess($ih#s0#0, $ih#t0#0)
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.LexLess_h($LS($LZ), $ih#_k0#0, $ih#s0#0, $ih#t0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(74,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(79,28)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0 := _k#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := s#1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0 := t#1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.EquivalenceTheorem0__Lemma(k##0, s##0, t##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(79,37)"} true;
    }
    else
    {
    }
}



procedure {:_induction k#0, s#0, t#0} CheckWellformed$$_module.__default.EquivalenceTheorem0__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0, s#0, t#0} Call$$_module.__default.EquivalenceTheorem0__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  // user-defined preconditions
  requires !_module.__default.NotLexLess_k($LS($LS($LZ)), k#0, s#0, t#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(k#0, s#0, t#0);
  free ensures _module.__default.LexLess_h#canCall(k#0, s#0, t#0)
     && 
    _module.__default.LexLess_h($LS($LZ), k#0, s#0, t#0)
     && (0 < k#0
       ==> $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
         && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
           ==> _module.__default.LexLess_h($LS($LZ), k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, s#0, t#0} Impl$$_module.__default.EquivalenceTheorem0__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0))
   returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.__default.NotLexLess_k($LS($LS($LZ)), k#0, s#0, t#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LexLess_h#canCall(k#0, s#0, t#0);
  ensures _module.__default.LexLess_h#canCall(k#0, s#0, t#0)
     ==> _module.__default.LexLess_h($LS($LZ), k#0, s#0, t#0)
       || (0 < k#0
         ==> $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int);
  ensures _module.__default.LexLess_h#canCall(k#0, s#0, t#0)
     ==> _module.__default.LexLess_h($LS($LZ), k#0, s#0, t#0)
       || (0 < k#0
         ==> 
        $Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
         ==> _module.__default.LexLess_h($LS($LS($LZ)), k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, s#0, t#0} Impl$$_module.__default.EquivalenceTheorem0__Lemma(k#0: int, s#0: DatatypeType, t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: EquivalenceTheorem0_Lemma, Impl$$_module.__default.EquivalenceTheorem0__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(87,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    assume $IsA#_module.Stream(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#s0#0: DatatypeType, $ih#t0#0: DatatypeType :: 
      LitInt(0) <= $ih#k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && !_module.__default.NotLexLess_k($LS($LZ), $ih#k0#0, $ih#s0#0, $ih#t0#0)
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> _module.__default.LexLess_h($LS($LZ), $ih#k0#0, $ih#s0#0, $ih#t0#0));
    $_reverifyPost := false;
}



procedure {:_induction s#0, t#0} CheckWellformed$$_module.__default.EquivalenceTheorem1(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, t#0} Call$$_module.__default.EquivalenceTheorem1(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int;
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess#canCall(s#0, t#0);
  ensures !_module.__default.NotLexLess(s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, t#0} Impl$$_module.__default.EquivalenceTheorem1(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0))
   returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.LexLess#canCall(s#0, t#0)
     && 
    _module.__default.LexLess($LS($LZ), s#0, t#0)
     && 
    $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
     && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess#canCall(s#0, t#0);
  ensures !_module.__default.NotLexLess(s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, t#0} Impl$$_module.__default.EquivalenceTheorem1(s#0: DatatypeType, t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var k#0: int;
  var k##0: int;
  var s##0: DatatypeType;
  var t##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: EquivalenceTheorem1, Impl$$_module.__default.EquivalenceTheorem1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(93,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    assume $IsA#_module.Stream(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#t0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && _module.__default.LexLess($LS($LZ), $ih#s0#0, $ih#t0#0)
           && false
         ==> !_module.__default.NotLexLess($ih#s0#0, $ih#t0#0));
    $_reverifyPost := false;
    // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(97,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc k#0;
        assume LitInt(0) <= k#0;
        assume true;
        assume true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(98,30)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0 := k#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0 := t#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.EquivalenceTheorem1__Lemma(k##0, s##0, t##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(98,38)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall k#1: int :: 
          { _module.__default.NotLexLess_k($LS($LZ), k#1, s#0, t#0) } 
          LitInt(0) <= k#1 && Lit(true)
             ==> !_module.__default.NotLexLess_k($LS($LZ), k#1, s#0, t#0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(99,2)"} true;
}



procedure {:_induction k#0, s#0, t#0} CheckWellformed$$_module.__default.EquivalenceTheorem1__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0, s#0, t#0} Call$$_module.__default.EquivalenceTheorem1__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int;
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess_k#canCall(k#0, s#0, t#0);
  ensures !_module.__default.NotLexLess_k($LS($LS($LZ)), k#0, s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, s#0, t#0} Impl$$_module.__default.EquivalenceTheorem1__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0))
   returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.LexLess#canCall(s#0, t#0)
     && 
    _module.__default.LexLess($LS($LZ), s#0, t#0)
     && 
    $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int
     && ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess_k#canCall(k#0, s#0, t#0);
  ensures !_module.__default.NotLexLess_k($LS($LS($LZ)), k#0, s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, s#0, t#0} Impl$$_module.__default.EquivalenceTheorem1__Lemma(k#0: int, s#0: DatatypeType, t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: EquivalenceTheorem1_Lemma, Impl$$_module.__default.EquivalenceTheorem1__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(104,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    assume $IsA#_module.Stream(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#s0#0: DatatypeType, $ih#t0#0: DatatypeType :: 
      LitInt(0) <= $ih#k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && _module.__default.LexLess($LS($LZ), $ih#s0#0, $ih#t0#0)
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> !_module.__default.NotLexLess_k($LS($LZ), $ih#k0#0, $ih#s0#0, $ih#t0#0));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Theorem1__Alt(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem1__Alt(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  // user-defined preconditions
  requires _module.__default.NotLexLess#canCall(s#0, u#0)
     ==> _module.__default.NotLexLess(s#0, u#0)
       || (exists k#0: int :: 
        { _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, u#0) } 
        LitInt(0) <= k#0 && _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, u#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess#canCall(s#0, t#0)
     && (!_module.__default.NotLexLess(s#0, t#0)
       ==> _module.__default.NotLexLess#canCall(t#0, u#0));
  ensures _module.__default.NotLexLess(s#0, t#0) || _module.__default.NotLexLess(t#0, u#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Theorem1__Alt(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0))
   returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.NotLexLess#canCall(s#0, u#0)
     && 
    _module.__default.NotLexLess(s#0, u#0)
     && (exists k#1: int :: 
      { _module.__default.NotLexLess_k($LS($LZ), k#1, s#0, u#0) } 
      LitInt(0) <= k#1 && _module.__default.NotLexLess_k($LS($LZ), k#1, s#0, u#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess#canCall(s#0, t#0)
     && (!_module.__default.NotLexLess(s#0, t#0)
       ==> _module.__default.NotLexLess#canCall(t#0, u#0));
  ensures _module.__default.NotLexLess(s#0, t#0) || _module.__default.NotLexLess(t#0, u#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Theorem1__Alt(s#0: DatatypeType, t#0: DatatypeType, u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#2: int;
  var ##k#0: int;
  var ##s#3: DatatypeType;
  var ##t#3: DatatypeType;
  var k##0: int;
  var s##0: DatatypeType;
  var t##0: DatatypeType;
  var u##0: DatatypeType;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem1_Alt, Impl$$_module.__default.Theorem1__Alt
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(110,0): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(111,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc k#2;
        assume LitInt(0) <= k#2;
        ##k#0 := k#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##k#0, Tclass._System.nat(), $Heap);
        ##s#3 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#3, Tclass._module.Stream(TInt), $Heap);
        ##t#3 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#3, Tclass._module.Stream(TInt), $Heap);
        assume _module.__default.NotLexLess_k#canCall(k#2, s#0, u#0);
        assume _module.__default.NotLexLess_k#canCall(k#2, s#0, u#0);
        assume _module.__default.NotLexLess_k($LS($LZ), k#2, s#0, u#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(112,23)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0 := k#2;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0 := t#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        u##0 := u#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Theorem1__Alt__Lemma(k##0, s##0, t##0, u##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(112,34)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#0 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#0 == $Heap;
        assume (forall k#3: int :: 
          { _module.__default.NotLexLess_k($LS($LZ), k#3, t#0, u#0) } 
            { _module.__default.NotLexLess_k($LS($LZ), k#3, s#0, t#0) } 
            { _module.__default.NotLexLess_k($LS($LZ), k#3, s#0, u#0) } 
          LitInt(0) <= k#3 && _module.__default.NotLexLess_k($LS($LZ), k#3, s#0, u#0)
             ==> _module.__default.NotLexLess_k($LS($LZ), k#3, s#0, t#0)
               || _module.__default.NotLexLess_k($LS($LZ), k#3, t#0, u#0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(113,2)"} true;
}



procedure {:_induction k#0, s#0, t#0, u#0} CheckWellformed$$_module.__default.Theorem1__Alt__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0, s#0, t#0, u#0} Call$$_module.__default.Theorem1__Alt__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0));
  // user-defined preconditions
  requires _module.__default.NotLexLess_k#canCall(k#0, s#0, u#0)
     ==> _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, u#0)
       || (k#0 == LitInt(0) ==> Lit(false));
  requires _module.__default.NotLexLess_k#canCall(k#0, s#0, u#0)
     ==> _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, u#0)
       || (k#0 != LitInt(0)
         ==> !($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(u#0)): int)
           || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(u#0)): int
             && _module.__default.NotLexLess_k($LS($LS($LZ)), k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(u#0))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess_k#canCall(k#0, s#0, t#0)
     && (!_module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0)
       ==> _module.__default.NotLexLess_k#canCall(k#0, t#0, u#0));
  ensures _module.__default.NotLexLess_k($LS($LS($LZ)), k#0, s#0, t#0)
     || _module.__default.NotLexLess_k($LS($LS($LZ)), k#0, t#0, u#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, s#0, t#0, u#0} Impl$$_module.__default.Theorem1__Alt__Lemma(k#0: int where LitInt(0) <= k#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0))
   returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.NotLexLess_k#canCall(k#0, s#0, u#0)
     && 
    _module.__default.NotLexLess_k($LS($LZ), k#0, s#0, u#0)
     && (if k#0 == LitInt(0)
       then false
       else !($Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(u#0)): int)
         || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(u#0)): int
           && _module.__default.NotLexLess_k($LS($LZ), k#0 - 1, _module.Stream.tl(s#0), _module.Stream.tl(u#0))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.NotLexLess_k#canCall(k#0, s#0, t#0)
     && (!_module.__default.NotLexLess_k($LS($LZ), k#0, s#0, t#0)
       ==> _module.__default.NotLexLess_k#canCall(k#0, t#0, u#0));
  ensures _module.__default.NotLexLess_k($LS($LS($LZ)), k#0, s#0, t#0)
     || _module.__default.NotLexLess_k($LS($LS($LZ)), k#0, t#0, u#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, s#0, t#0, u#0} Impl$$_module.__default.Theorem1__Alt__Lemma(k#0: int, s#0: DatatypeType, t#0: DatatypeType, u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem1_Alt_Lemma, Impl$$_module.__default.Theorem1__Alt__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(118,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    assume $IsA#_module.Stream(t#0);
    assume $IsA#_module.Stream(u#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, 
        $ih#s0#0: DatatypeType, 
        $ih#t0#0: DatatypeType, 
        $ih#u0#0: DatatypeType :: 
      LitInt(0) <= $ih#k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && $Is($ih#u0#0, Tclass._module.Stream(TInt))
           && _module.__default.NotLexLess_k($LS($LZ), $ih#k0#0, $ih#s0#0, $ih#u0#0)
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> _module.__default.NotLexLess_k($LS($LZ), $ih#k0#0, $ih#s0#0, $ih#t0#0)
           || _module.__default.NotLexLess_k($LS($LZ), $ih#k0#0, $ih#t0#0, $ih#u0#0));
    $_reverifyPost := false;
}



// function declaration for _module._default.PointwiseAdd
function _module.__default.PointwiseAdd($ly: LayerType, s#0: DatatypeType, t#0: DatatypeType) : DatatypeType;

function _module.__default.PointwiseAdd#canCall(s#0: DatatypeType, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.PointwiseAdd($LS($ly), s#0, t#0) } 
  _module.__default.PointwiseAdd($LS($ly), s#0, t#0)
     == _module.__default.PointwiseAdd($ly, s#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.PointwiseAdd(AsFuelBottom($ly), s#0, t#0) } 
  _module.__default.PointwiseAdd($ly, s#0, t#0)
     == _module.__default.PointwiseAdd($LZ, s#0, t#0));

// consequence axiom for _module.__default.PointwiseAdd
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.PointwiseAdd($ly, s#0, t#0) } 
    _module.__default.PointwiseAdd#canCall(s#0, t#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> $Is(_module.__default.PointwiseAdd($ly, s#0, t#0), Tclass._module.Stream(TInt)));

function _module.__default.PointwiseAdd#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.PointwiseAdd
axiom (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
  { _module.__default.PointwiseAdd#requires($ly, s#0, t#0) } 
  $Is(s#0, Tclass._module.Stream(TInt)) && $Is(t#0, Tclass._module.Stream(TInt))
     ==> _module.__default.PointwiseAdd#requires($ly, s#0, t#0) == true);

// definition axiom for _module.__default.PointwiseAdd (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, t#0: DatatypeType :: 
    { _module.__default.PointwiseAdd($LS($ly), s#0, t#0) } 
    _module.__default.PointwiseAdd#canCall(s#0, t#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(TInt))
           && $Is(t#0, Tclass._module.Stream(TInt)))
       ==> _module.Stream.Cons_q(s#0)
         && _module.Stream.Cons_q(t#0)
         && 
        _module.Stream.Cons_q(s#0)
         && _module.Stream.Cons_q(t#0)
         && _module.__default.PointwiseAdd#canCall(_module.Stream.tl(s#0), _module.Stream.tl(t#0))
         && _module.__default.PointwiseAdd($LS($ly), s#0, t#0)
           == #_module.Stream.Cons($Box($Unbox(_module.Stream.hd(s#0)): int + $Unbox(_module.Stream.hd(t#0)): int), 
            _module.__default.PointwiseAdd($ly, _module.Stream.tl(s#0), _module.Stream.tl(t#0))));

procedure CheckWellformed$$_module.__default.PointwiseAdd(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(TInt)), 
    t#0: DatatypeType where $Is(t#0, Tclass._module.Stream(TInt)));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.PointwiseAdd(s#0: DatatypeType, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##t#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function PointwiseAdd
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(121,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.PointwiseAdd($LS($LZ), s#0, t#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(t#0);
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(t#0);
        ##s#0 := _module.Stream.tl(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
        ##t#0 := _module.Stream.tl(t#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, Tclass._module.Stream(TInt), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.PointwiseAdd#canCall(_module.Stream.tl(s#0), _module.Stream.tl(t#0));
        assume _module.Stream.Cons_q(_module.__default.PointwiseAdd($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
        assume _module.__default.PointwiseAdd($LS($LZ), s#0, t#0)
           == #_module.Stream.Cons($Box($Unbox(_module.Stream.hd(s#0)): int + $Unbox(_module.Stream.hd(t#0)): int), 
            _module.__default.PointwiseAdd($LS($LZ), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
        assume _module.Stream.Cons_q(s#0)
           && _module.Stream.Cons_q(t#0)
           && 
          _module.Stream.Cons_q(s#0)
           && _module.Stream.Cons_q(t#0)
           && _module.__default.PointwiseAdd#canCall(_module.Stream.tl(s#0), _module.Stream.tl(t#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.PointwiseAdd($LS($LZ), s#0, t#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.Theorem2__Pointwise__Addition__Is__Monotone(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0), 
    v#0: DatatypeType
       where $Is(v#0, Tclass._module.Stream(TInt))
         && $IsAlloc(v#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(v#0));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem2__Pointwise__Addition__Is__Monotone(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(TInt))
         && $IsAlloc(s#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(TInt))
         && $IsAlloc(t#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(TInt))
         && $IsAlloc(u#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#0), 
    v#0: DatatypeType
       where $Is(v#0, Tclass._module.Stream(TInt))
         && $IsAlloc(v#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(v#0));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || $Unbox(_module.Stream.hd(s#0)): int <= $Unbox(_module.Stream.hd(t#0)): int;
  requires _module.__default.LexLess#canCall(s#0, t#0)
     ==> _module.__default.LexLess($LS($LZ), s#0, t#0)
       || ($Unbox(_module.Stream.hd(s#0)): int == $Unbox(_module.Stream.hd(t#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
  requires _module.__default.LexLess#canCall(u#0, v#0)
     ==> _module.__default.LexLess($LS($LZ), u#0, v#0)
       || $Unbox(_module.Stream.hd(u#0)): int <= $Unbox(_module.Stream.hd(v#0)): int;
  requires _module.__default.LexLess#canCall(u#0, v#0)
     ==> _module.__default.LexLess($LS($LZ), u#0, v#0)
       || ($Unbox(_module.Stream.hd(u#0)): int == $Unbox(_module.Stream.hd(v#0)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(u#0), _module.Stream.tl(v#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PointwiseAdd#canCall(s#0, u#0)
     && _module.__default.PointwiseAdd#canCall(t#0, v#0)
     && _module.__default.LexLess#canCall(_module.__default.PointwiseAdd($LS($LZ), s#0, u#0), 
      _module.__default.PointwiseAdd($LS($LZ), t#0, v#0));
  free ensures _module.__default.LexLess#canCall(_module.__default.PointwiseAdd($LS($LZ), s#0, u#0), 
      _module.__default.PointwiseAdd($LS($LZ), t#0, v#0))
     && 
    _module.__default.LexLess($LS($LZ), 
      _module.__default.PointwiseAdd($LS($LZ), s#0, u#0), 
      _module.__default.PointwiseAdd($LS($LZ), t#0, v#0))
     && 
    $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), s#0, u#0))): int
       <= $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), t#0, v#0))): int
     && ($Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), s#0, u#0))): int
         == $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), t#0, v#0))): int
       ==> _module.__default.LexLess($LS($LZ), 
        _module.Stream.tl(_module.__default.PointwiseAdd($LS($LZ), s#0, u#0)), 
        _module.Stream.tl(_module.__default.PointwiseAdd($LS($LZ), t#0, v#0))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1, u#1, v#1} CoCall$$_module.__default.Theorem2__Pointwise__Addition__Is__Monotone_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(TInt))
         && $IsAlloc(u#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#1), 
    v#1: DatatypeType
       where $Is(v#1, Tclass._module.Stream(TInt))
         && $IsAlloc(v#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(v#1));
  // user-defined preconditions
  requires _module.__default.LexLess#canCall(s#1, t#1)
     ==> _module.__default.LexLess($LS($LZ), s#1, t#1)
       || $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int;
  requires _module.__default.LexLess#canCall(s#1, t#1)
     ==> _module.__default.LexLess($LS($LZ), s#1, t#1)
       || ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(s#1), _module.Stream.tl(t#1)));
  requires _module.__default.LexLess#canCall(u#1, v#1)
     ==> _module.__default.LexLess($LS($LZ), u#1, v#1)
       || $Unbox(_module.Stream.hd(u#1)): int <= $Unbox(_module.Stream.hd(v#1)): int;
  requires _module.__default.LexLess#canCall(u#1, v#1)
     ==> _module.__default.LexLess($LS($LZ), u#1, v#1)
       || ($Unbox(_module.Stream.hd(u#1)): int == $Unbox(_module.Stream.hd(v#1)): int
         ==> _module.__default.LexLess($LS($LS($LZ)), _module.Stream.tl(u#1), _module.Stream.tl(v#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PointwiseAdd#canCall(s#1, u#1)
     && _module.__default.PointwiseAdd#canCall(t#1, v#1)
     && _module.__default.LexLess_h#canCall(_k#0, 
      _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
      _module.__default.PointwiseAdd($LS($LZ), t#1, v#1));
  free ensures _module.__default.LexLess_h#canCall(_k#0, 
      _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
      _module.__default.PointwiseAdd($LS($LZ), t#1, v#1))
     && 
    _module.__default.LexLess_h($LS($LZ), 
      _k#0, 
      _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
      _module.__default.PointwiseAdd($LS($LZ), t#1, v#1))
     && (0 < _k#0
       ==> $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), s#1, u#1))): int
           <= $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), t#1, v#1))): int
         && ($Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), s#1, u#1))): int
             == $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), t#1, v#1))): int
           ==> _module.__default.LexLess_h($LS($LZ), 
            _k#0 - 1, 
            _module.Stream.tl(_module.__default.PointwiseAdd($LS($LZ), s#1, u#1)), 
            _module.Stream.tl(_module.__default.PointwiseAdd($LS($LZ), t#1, v#1)))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1, u#1, v#1} Impl$$_module.__default.Theorem2__Pointwise__Addition__Is__Monotone_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(TInt))
         && $IsAlloc(s#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(TInt))
         && $IsAlloc(t#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(t#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(TInt))
         && $IsAlloc(u#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(u#1), 
    v#1: DatatypeType
       where $Is(v#1, Tclass._module.Stream(TInt))
         && $IsAlloc(v#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(v#1))
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.LexLess#canCall(s#1, t#1)
     && 
    _module.__default.LexLess($LS($LZ), s#1, t#1)
     && 
    $Unbox(_module.Stream.hd(s#1)): int <= $Unbox(_module.Stream.hd(t#1)): int
     && ($Unbox(_module.Stream.hd(s#1)): int == $Unbox(_module.Stream.hd(t#1)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(s#1), _module.Stream.tl(t#1)));
  free requires _module.__default.LexLess#canCall(u#1, v#1)
     && 
    _module.__default.LexLess($LS($LZ), u#1, v#1)
     && 
    $Unbox(_module.Stream.hd(u#1)): int <= $Unbox(_module.Stream.hd(v#1)): int
     && ($Unbox(_module.Stream.hd(u#1)): int == $Unbox(_module.Stream.hd(v#1)): int
       ==> _module.__default.LexLess($LS($LZ), _module.Stream.tl(u#1), _module.Stream.tl(v#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PointwiseAdd#canCall(s#1, u#1)
     && _module.__default.PointwiseAdd#canCall(t#1, v#1)
     && _module.__default.LexLess_h#canCall(_k#0, 
      _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
      _module.__default.PointwiseAdd($LS($LZ), t#1, v#1));
  ensures _module.__default.LexLess_h#canCall(_k#0, 
      _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
      _module.__default.PointwiseAdd($LS($LZ), t#1, v#1))
     ==> _module.__default.LexLess_h($LS($LZ), 
        _k#0, 
        _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
        _module.__default.PointwiseAdd($LS($LZ), t#1, v#1))
       || (0 < _k#0
         ==> $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LS($LZ)), s#1, u#1))): int
           <= $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LS($LZ)), t#1, v#1))): int);
  ensures _module.__default.LexLess_h#canCall(_k#0, 
      _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
      _module.__default.PointwiseAdd($LS($LZ), t#1, v#1))
     ==> _module.__default.LexLess_h($LS($LZ), 
        _k#0, 
        _module.__default.PointwiseAdd($LS($LZ), s#1, u#1), 
        _module.__default.PointwiseAdd($LS($LZ), t#1, v#1))
       || (0 < _k#0
         ==> 
        $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), s#1, u#1))): int
           == $Unbox(_module.Stream.hd(_module.__default.PointwiseAdd($LS($LZ), t#1, v#1))): int
         ==> _module.__default.LexLess_h($LS($LS($LZ)), 
          _k#0 - 1, 
          _module.Stream.tl(_module.__default.PointwiseAdd($LS($LS($LZ)), s#1, u#1)), 
          _module.Stream.tl(_module.__default.PointwiseAdd($LS($LS($LZ)), t#1, v#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, t#1, u#1, v#1} Impl$$_module.__default.Theorem2__Pointwise__Addition__Is__Monotone_h(_k#0: int, 
    s#1: DatatypeType, 
    t#1: DatatypeType, 
    u#1: DatatypeType, 
    v#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem2_Pointwise_Addition_Is_Monotone#, Impl$$_module.__default.Theorem2__Pointwise__Addition__Is__Monotone_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(126,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(t#1);
    assume $IsA#_module.Stream(u#1);
    assume $IsA#_module.Stream(v#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, 
        $ih#s0#0: DatatypeType, 
        $ih#t0#0: DatatypeType, 
        $ih#u0#0: DatatypeType, 
        $ih#v0#0: DatatypeType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(TInt))
           && $Is($ih#t0#0, Tclass._module.Stream(TInt))
           && $Is($ih#u0#0, Tclass._module.Stream(TInt))
           && $Is($ih#v0#0, Tclass._module.Stream(TInt))
           && 
          _module.__default.LexLess($LS($LZ), $ih#s0#0, $ih#t0#0)
           && _module.__default.LexLess($LS($LZ), $ih#u0#0, $ih#v0#0)
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.LexLess_h($LS($LZ), 
          $ih#_k0#0, 
          _module.__default.PointwiseAdd($LS($LZ), $ih#s0#0, $ih#u0#0), 
          _module.__default.PointwiseAdd($LS($LZ), $ih#t0#0, $ih#v0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(129,1)
    assume true;
    if (0 < _k#0)
    {
    }
    else
    {
    }
}



// function declaration for _module._default.Subtype
function _module.__default.Subtype($ly: LayerType, a#0: DatatypeType, b#0: DatatypeType) : bool;

function _module.__default.Subtype#canCall(a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.Subtype($LS($ly), a#0, b#0) } 
  _module.__default.Subtype($LS($ly), a#0, b#0)
     == _module.__default.Subtype($ly, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.Subtype(AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.Subtype($ly, a#0, b#0)
     == _module.__default.Subtype($LZ, a#0, b#0));

// consequence axiom for _module.__default.Subtype
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.Subtype($ly, a#0, b#0) } 
    _module.__default.Subtype#canCall(a#0, b#0)
         || (17 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.RecType())
           && $Is(b#0, Tclass._module.RecType()))
       ==> true);

function _module.__default.Subtype#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Subtype
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.Subtype#requires($ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.RecType()) && $Is(b#0, Tclass._module.RecType())
     ==> _module.__default.Subtype#requires($ly, a#0, b#0) == true);

// definition axiom for _module.__default.Subtype (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.Subtype($LS($ly), a#0, b#0) } 
    _module.__default.Subtype#canCall(a#0, b#0)
         || (17 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.RecType())
           && $Is(b#0, Tclass._module.RecType()))
       ==> $IsA#_module.RecType(a#0)
         && (!$Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
           ==> $IsA#_module.RecType(b#0)
             && (!$Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
               ==> 
              _module.RecType.Arrow_q(a#0)
               ==> 
              _module.RecType.Arrow_q(b#0)
               ==> _module.__default.Subtype#canCall(_module.RecType.dom(b#0), _module.RecType.dom(a#0))
                 && (_module.__default.Subtype($ly, _module.RecType.dom(b#0), _module.RecType.dom(a#0))
                   ==> _module.__default.Subtype#canCall(_module.RecType.ran(a#0), _module.RecType.ran(b#0)))))
         && _module.__default.Subtype($LS($ly), a#0, b#0)
           == (
            $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
             || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
             || (
              _module.RecType.Arrow_q(a#0)
               && _module.RecType.Arrow_q(b#0)
               && _module.__default.Subtype($ly, _module.RecType.dom(b#0), _module.RecType.dom(a#0))
               && _module.__default.Subtype($ly, _module.RecType.ran(a#0), _module.RecType.ran(b#0)))));

// 1st prefix predicate axiom for _module.__default.Subtype_h
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.Subtype($LS($ly), a#0, b#0) } 
    $Is(a#0, Tclass._module.RecType())
         && $Is(b#0, Tclass._module.RecType())
         && _module.__default.Subtype($LS($ly), a#0, b#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0) } 
        _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0)));

// 2nd prefix predicate axiom
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.Subtype($LS($ly), a#0, b#0) } 
    $Is(a#0, Tclass._module.RecType())
         && $Is(b#0, Tclass._module.RecType())
         && (forall _k#0: Box :: 
          { _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0) } 
          _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0))
       ==> _module.__default.Subtype($LS($ly), a#0, b#0));

// 3rd prefix predicate axiom
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType, _k#0: Box :: 
    { _module.__default.Subtype_h($ly, _k#0, a#0, b#0) } 
    $Is(a#0, Tclass._module.RecType())
         && $Is(b#0, Tclass._module.RecType())
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.Subtype_h($ly, _k#0, a#0, b#0));

procedure CheckWellformed$$_module.__default.Subtype(a#0: DatatypeType where $Is(a#0, Tclass._module.RecType()), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.RecType()));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Subtype(a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##a#1: DatatypeType;
  var ##b#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Subtype
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(151,19): initial state"} true;
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
        if (!$Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom()))
        {
        }

        if (!($Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
           || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())))
        {
            if (_module.RecType.Arrow_q(a#0))
            {
            }

            if (_module.RecType.Arrow_q(a#0) && _module.RecType.Arrow_q(b#0))
            {
                assert _module.RecType.Arrow_q(b#0);
                assert _module.RecType.Arrow_q(a#0);
                ##a#0 := _module.RecType.dom(b#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, Tclass._module.RecType(), $Heap);
                ##b#0 := _module.RecType.dom(a#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, Tclass._module.RecType(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Subtype#canCall(_module.RecType.dom(b#0), _module.RecType.dom(a#0));
            }

            if (_module.RecType.Arrow_q(a#0)
               && _module.RecType.Arrow_q(b#0)
               && _module.__default.Subtype($LS($LZ), _module.RecType.dom(b#0), _module.RecType.dom(a#0)))
            {
                assert _module.RecType.Arrow_q(a#0);
                assert _module.RecType.Arrow_q(b#0);
                ##a#1 := _module.RecType.ran(a#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#1, Tclass._module.RecType(), $Heap);
                ##b#1 := _module.RecType.ran(b#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#1, Tclass._module.RecType(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Subtype#canCall(_module.RecType.ran(a#0), _module.RecType.ran(b#0));
            }
        }

        assume _module.__default.Subtype($LS($LZ), a#0, b#0)
           == (
            $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
             || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
             || (
              _module.RecType.Arrow_q(a#0)
               && _module.RecType.Arrow_q(b#0)
               && _module.__default.Subtype($LS($LZ), _module.RecType.dom(b#0), _module.RecType.dom(a#0))
               && _module.__default.Subtype($LS($LZ), _module.RecType.ran(a#0), _module.RecType.ran(b#0))));
        assume $IsA#_module.RecType(a#0)
           && (!$Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
             ==> $IsA#_module.RecType(b#0)
               && (!$Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
                 ==> 
                _module.RecType.Arrow_q(a#0)
                 ==> 
                _module.RecType.Arrow_q(b#0)
                 ==> _module.__default.Subtype#canCall(_module.RecType.dom(b#0), _module.RecType.dom(a#0))
                   && (_module.__default.Subtype($LS($LZ), _module.RecType.dom(b#0), _module.RecType.dom(a#0))
                     ==> _module.__default.Subtype#canCall(_module.RecType.ran(a#0), _module.RecType.ran(b#0)))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Subtype($LS($LZ), a#0, b#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.Subtype#
function _module.__default.Subtype_h($ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType) : bool;

function _module.__default.Subtype_h#canCall(_k#0: Box, a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0) } 
  _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0)
     == _module.__default.Subtype_h($ly, _k#0, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.Subtype_h(AsFuelBottom($ly), _k#0, a#0, b#0) } 
  _module.__default.Subtype_h($ly, _k#0, a#0, b#0)
     == _module.__default.Subtype_h($LZ, _k#0, a#0, b#0));

// consequence axiom for _module.__default.Subtype_h
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.Subtype_h($ly, _k#0, a#0, b#0) } 
    _module.__default.Subtype_h#canCall(_k#0, a#0, b#0)
         || (18 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.RecType())
           && $Is(b#0, Tclass._module.RecType()))
       ==> true);

function _module.__default.Subtype_h#requires(LayerType, Box, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Subtype_h
axiom (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.Subtype_h#requires($ly, _k#0, a#0, b#0) } 
  $Is(a#0, Tclass._module.RecType()) && $Is(b#0, Tclass._module.RecType())
     ==> _module.__default.Subtype_h#requires($ly, _k#0, a#0, b#0) == true);

// definition axiom for _module.__default.Subtype_h (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0) } 
    _module.__default.Subtype_h#canCall(_k#0, a#0, b#0)
         || (18 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.RecType())
           && $Is(b#0, Tclass._module.RecType()))
       ==> (0 < ORD#Offset(_k#0)
           ==> $IsA#_module.RecType(a#0)
             && (!$Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
               ==> $IsA#_module.RecType(b#0)
                 && (!$Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
                   ==> 
                  _module.RecType.Arrow_q(a#0)
                   ==> 
                  _module.RecType.Arrow_q(b#0)
                   ==> _module.__default.Subtype_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                      _module.RecType.dom(b#0), 
                      _module.RecType.dom(a#0))
                     && (_module.__default.Subtype_h($ly, 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        _module.RecType.dom(b#0), 
                        _module.RecType.dom(a#0))
                       ==> _module.__default.Subtype_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                        _module.RecType.ran(a#0), 
                        _module.RecType.ran(b#0))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
             || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
             || (
              _module.RecType.Arrow_q(a#0)
               && _module.RecType.Arrow_q(b#0)
               && _module.__default.Subtype_h($ly, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.RecType.dom(b#0), 
                _module.RecType.dom(a#0))
               && _module.__default.Subtype_h($ly, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.RecType.ran(a#0), 
                _module.RecType.ran(b#0))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.Subtype_h($ly, _k'#0, a#0, b#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.__default.Subtype_h#canCall(_k'#0, a#0, b#0)))
         && _module.__default.Subtype_h($LS($ly), _k#0, a#0, b#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
                 || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
                 || (
                  _module.RecType.Arrow_q(a#0)
                   && _module.RecType.Arrow_q(b#0)
                   && _module.__default.Subtype_h($ly, 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.RecType.dom(b#0), 
                    _module.RecType.dom(a#0))
                   && _module.__default.Subtype_h($ly, 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.RecType.ran(a#0), 
                    _module.RecType.ran(b#0))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.Subtype_h($ly, _k'#0, a#0, b#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.Subtype_h($ly, _k'#0, a#0, b#0)))));

// definition axiom for _module.__default.Subtype_h for decreasing-related literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.Subtype_h($LS($ly), Lit(_k#0), a#0, b#0) } 
    _module.__default.Subtype_h#canCall(Lit(_k#0), a#0, b#0)
         || (18 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.RecType())
           && $Is(b#0, Tclass._module.RecType()))
       ==> (0 < ORD#Offset(_k#0)
           ==> $IsA#_module.RecType(a#0)
             && (!$Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
               ==> $IsA#_module.RecType(b#0)
                 && (!$Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
                   ==> 
                  _module.RecType.Arrow_q(a#0)
                   ==> 
                  _module.RecType.Arrow_q(b#0)
                   ==> _module.__default.Subtype_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                      _module.RecType.dom(b#0), 
                      _module.RecType.dom(a#0))
                     && (_module.__default.Subtype_h($LS($ly), 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        _module.RecType.dom(b#0), 
                        _module.RecType.dom(a#0))
                       ==> _module.__default.Subtype_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                        _module.RecType.ran(a#0), 
                        _module.RecType.ran(b#0))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
             || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
             || (
              _module.RecType.Arrow_q(a#0)
               && _module.RecType.Arrow_q(b#0)
               && _module.__default.Subtype_h($LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.RecType.dom(b#0), 
                _module.RecType.dom(a#0))
               && _module.__default.Subtype_h($LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.RecType.ran(a#0), 
                _module.RecType.ran(b#0))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.Subtype_h($LS($ly), _k'#1, a#0, b#0) } 
            ORD#Less(_k'#1, _k#0) ==> _module.__default.Subtype_h#canCall(_k'#1, a#0, b#0)))
         && _module.__default.Subtype_h($LS($ly), Lit(_k#0), a#0, b#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
                 || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
                 || (
                  _module.RecType.Arrow_q(a#0)
                   && _module.RecType.Arrow_q(b#0)
                   && _module.__default.Subtype_h($LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.RecType.dom(b#0), 
                    _module.RecType.dom(a#0))
                   && _module.__default.Subtype_h($LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.RecType.ran(a#0), 
                    _module.RecType.ran(b#0))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.Subtype_h($LS($ly), _k'#1, a#0, b#0) } 
                ORD#Less(_k'#1, _k#0) ==> _module.__default.Subtype_h($LS($ly), _k'#1, a#0, b#0)))));

// definition axiom for _module.__default.Subtype_h for all literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.Subtype_h($LS($ly), Lit(_k#0), Lit(a#0), Lit(b#0)) } 
    _module.__default.Subtype_h#canCall(Lit(_k#0), Lit(a#0), Lit(b#0))
         || (18 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.RecType())
           && $Is(b#0, Tclass._module.RecType()))
       ==> (0 < ORD#Offset(_k#0)
           ==> $IsA#_module.RecType(a#0)
             && (!$Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
               ==> $IsA#_module.RecType(b#0)
                 && (!$Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
                   ==> 
                  _module.RecType.Arrow_q(a#0)
                   ==> 
                  _module.RecType.Arrow_q(b#0)
                   ==> _module.__default.Subtype_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                      _module.RecType.dom(b#0), 
                      _module.RecType.dom(a#0))
                     && (_module.__default.Subtype_h($LS($ly), 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        _module.RecType.dom(b#0), 
                        _module.RecType.dom(a#0))
                       ==> _module.__default.Subtype_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                        _module.RecType.ran(a#0), 
                        _module.RecType.ran(b#0))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
             || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
             || (
              _module.RecType.Arrow_q(a#0)
               && _module.RecType.Arrow_q(b#0)
               && _module.__default.Subtype_h($LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.RecType.dom(b#0), 
                _module.RecType.dom(a#0))
               && _module.__default.Subtype_h($LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.RecType.ran(a#0), 
                _module.RecType.ran(b#0))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.Subtype_h($LS($ly), _k'#2, a#0, b#0) } 
            ORD#Less(_k'#2, _k#0) ==> _module.__default.Subtype_h#canCall(_k'#2, a#0, b#0)))
         && _module.__default.Subtype_h($LS($ly), Lit(_k#0), Lit(a#0), Lit(b#0))
           == ((0 < ORD#Offset(_k#0)
               ==> $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
                 || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
                 || (
                  _module.RecType.Arrow_q(a#0)
                   && _module.RecType.Arrow_q(b#0)
                   && _module.__default.Subtype_h($LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.RecType.dom(b#0), 
                    _module.RecType.dom(a#0))
                   && _module.__default.Subtype_h($LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.RecType.ran(a#0), 
                    _module.RecType.ran(b#0))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.Subtype_h($LS($ly), _k'#2, a#0, b#0) } 
                ORD#Less(_k'#2, _k#0) ==> _module.__default.Subtype_h($LS($ly), _k'#2, a#0, b#0)))));

procedure CheckWellformed$$_module.__default.Theorem3__Subtype__Is__Transitive(a#0: DatatypeType
       where $Is(a#0, Tclass._module.RecType())
         && $IsAlloc(a#0, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(a#0), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.RecType())
         && $IsAlloc(b#0, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.RecType())
         && $IsAlloc(c#0, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(c#0));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem3__Subtype__Is__Transitive(a#0: DatatypeType
       where $Is(a#0, Tclass._module.RecType())
         && $IsAlloc(a#0, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(a#0), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.RecType())
         && $IsAlloc(b#0, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.RecType())
         && $IsAlloc(c#0, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(c#0));
  // user-defined preconditions
  requires _module.__default.Subtype#canCall(a#0, b#0)
     ==> _module.__default.Subtype($LS($LZ), a#0, b#0)
       || 
      $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
       || $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Top())
       || (
        _module.RecType.Arrow_q(a#0)
         && _module.RecType.Arrow_q(b#0)
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.dom(b#0), _module.RecType.dom(a#0))
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.ran(a#0), _module.RecType.ran(b#0)));
  requires _module.__default.Subtype#canCall(b#0, c#0)
     ==> _module.__default.Subtype($LS($LZ), b#0, c#0)
       || 
      $Eq#_module.RecType($LS($LS($LZ)), b#0, #_module.RecType.Bottom())
       || $Eq#_module.RecType($LS($LS($LZ)), c#0, #_module.RecType.Top())
       || (
        _module.RecType.Arrow_q(b#0)
         && _module.RecType.Arrow_q(c#0)
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.dom(c#0), _module.RecType.dom(b#0))
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.ran(b#0), _module.RecType.ran(c#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Subtype#canCall(a#0, c#0);
  free ensures _module.__default.Subtype#canCall(a#0, c#0)
     && 
    _module.__default.Subtype($LS($LZ), a#0, c#0)
     && (
      $Eq#_module.RecType($LS($LS($LZ)), a#0, #_module.RecType.Bottom())
       || $Eq#_module.RecType($LS($LS($LZ)), c#0, #_module.RecType.Top())
       || (
        _module.RecType.Arrow_q(a#0)
         && _module.RecType.Arrow_q(c#0)
         && _module.__default.Subtype($LS($LZ), _module.RecType.dom(c#0), _module.RecType.dom(a#0))
         && _module.__default.Subtype($LS($LZ), _module.RecType.ran(a#0), _module.RecType.ran(c#0))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, a#1, b#1, c#1} CoCall$$_module.__default.Theorem3__Subtype__Is__Transitive_h(_k#0: Box, 
    a#1: DatatypeType
       where $Is(a#1, Tclass._module.RecType())
         && $IsAlloc(a#1, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(a#1), 
    b#1: DatatypeType
       where $Is(b#1, Tclass._module.RecType())
         && $IsAlloc(b#1, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(b#1), 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.RecType())
         && $IsAlloc(c#1, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(c#1));
  // user-defined preconditions
  requires _module.__default.Subtype#canCall(a#1, b#1)
     ==> _module.__default.Subtype($LS($LZ), a#1, b#1)
       || 
      $Eq#_module.RecType($LS($LS($LZ)), a#1, #_module.RecType.Bottom())
       || $Eq#_module.RecType($LS($LS($LZ)), b#1, #_module.RecType.Top())
       || (
        _module.RecType.Arrow_q(a#1)
         && _module.RecType.Arrow_q(b#1)
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.dom(b#1), _module.RecType.dom(a#1))
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.ran(a#1), _module.RecType.ran(b#1)));
  requires _module.__default.Subtype#canCall(b#1, c#1)
     ==> _module.__default.Subtype($LS($LZ), b#1, c#1)
       || 
      $Eq#_module.RecType($LS($LS($LZ)), b#1, #_module.RecType.Bottom())
       || $Eq#_module.RecType($LS($LS($LZ)), c#1, #_module.RecType.Top())
       || (
        _module.RecType.Arrow_q(b#1)
         && _module.RecType.Arrow_q(c#1)
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.dom(c#1), _module.RecType.dom(b#1))
         && _module.__default.Subtype($LS($LS($LZ)), _module.RecType.ran(b#1), _module.RecType.ran(c#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Subtype_h#canCall(_k#0, a#1, c#1);
  free ensures _module.__default.Subtype_h#canCall(_k#0, a#1, c#1)
     && 
    _module.__default.Subtype_h($LS($LZ), _k#0, a#1, c#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> $Eq#_module.RecType($LS($LS($LZ)), a#1, #_module.RecType.Bottom())
         || $Eq#_module.RecType($LS($LS($LZ)), c#1, #_module.RecType.Top())
         || (
          _module.RecType.Arrow_q(a#1)
           && _module.RecType.Arrow_q(c#1)
           && _module.__default.Subtype_h($LS($LZ), 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            _module.RecType.dom(c#1), 
            _module.RecType.dom(a#1))
           && _module.__default.Subtype_h($LS($LZ), 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            _module.RecType.ran(a#1), 
            _module.RecType.ran(c#1))))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.Subtype_h($LS($LZ), _k'#0, a#1, c#1) } 
        ORD#Less(_k'#0, _k#0) ==> _module.__default.Subtype_h($LS($LZ), _k'#0, a#1, c#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, a#1, b#1, c#1} Impl$$_module.__default.Theorem3__Subtype__Is__Transitive_h(_k#0: Box, 
    a#1: DatatypeType
       where $Is(a#1, Tclass._module.RecType())
         && $IsAlloc(a#1, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(a#1), 
    b#1: DatatypeType
       where $Is(b#1, Tclass._module.RecType())
         && $IsAlloc(b#1, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(b#1), 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.RecType())
         && $IsAlloc(c#1, Tclass._module.RecType(), $Heap)
         && $IsA#_module.RecType(c#1))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Subtype#canCall(a#1, b#1)
     && 
    _module.__default.Subtype($LS($LZ), a#1, b#1)
     && (
      $Eq#_module.RecType($LS($LS($LZ)), a#1, #_module.RecType.Bottom())
       || $Eq#_module.RecType($LS($LS($LZ)), b#1, #_module.RecType.Top())
       || (
        _module.RecType.Arrow_q(a#1)
         && _module.RecType.Arrow_q(b#1)
         && _module.__default.Subtype($LS($LZ), _module.RecType.dom(b#1), _module.RecType.dom(a#1))
         && _module.__default.Subtype($LS($LZ), _module.RecType.ran(a#1), _module.RecType.ran(b#1))));
  free requires _module.__default.Subtype#canCall(b#1, c#1)
     && 
    _module.__default.Subtype($LS($LZ), b#1, c#1)
     && (
      $Eq#_module.RecType($LS($LS($LZ)), b#1, #_module.RecType.Bottom())
       || $Eq#_module.RecType($LS($LS($LZ)), c#1, #_module.RecType.Top())
       || (
        _module.RecType.Arrow_q(b#1)
         && _module.RecType.Arrow_q(c#1)
         && _module.__default.Subtype($LS($LZ), _module.RecType.dom(c#1), _module.RecType.dom(b#1))
         && _module.__default.Subtype($LS($LZ), _module.RecType.ran(b#1), _module.RecType.ran(c#1))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Subtype_h#canCall(_k#0, a#1, c#1);
  ensures _module.__default.Subtype_h#canCall(_k#0, a#1, c#1)
     ==> _module.__default.Subtype_h($LS($LZ), _k#0, a#1, c#1)
       || (0 < ORD#Offset(_k#0)
         ==> $Eq#_module.RecType($LS($LS($LZ)), a#1, #_module.RecType.Bottom())
           || $Eq#_module.RecType($LS($LS($LZ)), c#1, #_module.RecType.Top())
           || (
            _module.RecType.Arrow_q(a#1)
             && _module.RecType.Arrow_q(c#1)
             && _module.__default.Subtype_h($LS($LS($LZ)), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.RecType.dom(c#1), 
              _module.RecType.dom(a#1))
             && _module.__default.Subtype_h($LS($LS($LZ)), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.RecType.ran(a#1), 
              _module.RecType.ran(c#1))));
  ensures _module.__default.Subtype_h#canCall(_k#0, a#1, c#1)
     ==> _module.__default.Subtype_h($LS($LZ), _k#0, a#1, c#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.Subtype_h($LS($LS($LZ)), _k'#1, a#1, c#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.Subtype_h($LS($LS($LZ)), _k'#1, a#1, c#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, a#1, b#1, c#1} Impl$$_module.__default.Theorem3__Subtype__Is__Transitive_h(_k#0: Box, a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem3_Subtype_Is_Transitive#, Impl$$_module.__default.Theorem3__Subtype__Is__Transitive_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(158,15): initial state"} true;
    assume $IsA#_module.RecType(a#1);
    assume $IsA#_module.RecType(b#1);
    assume $IsA#_module.RecType(c#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#a0#0: DatatypeType, 
        $ih#b0#0: DatatypeType, 
        $ih#c0#0: DatatypeType :: 
      $Is($ih#a0#0, Tclass._module.RecType())
           && $Is($ih#b0#0, Tclass._module.RecType())
           && $Is($ih#c0#0, Tclass._module.RecType())
           && 
          _module.__default.Subtype($LS($LZ), $ih#a0#0, $ih#b0#0)
           && _module.__default.Subtype($LS($LZ), $ih#b0#0, $ih#c0#0)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.Subtype_h($LS($LZ), $ih#_k0#0, $ih#a0#0, $ih#c0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(161,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(158,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, a#2: DatatypeType, b#2: DatatypeType, c#2: DatatypeType :: 
          $Is(a#2, Tclass._module.RecType())
               && $Is(b#2, Tclass._module.RecType())
               && $Is(c#2, Tclass._module.RecType())
               && 
              ORD#Less(_k'#2, _k#0)
               && 
              _module.__default.Subtype($LS($LZ), a#2, b#2)
               && _module.__default.Subtype($LS($LZ), b#2, c#2)
             ==> _module.__default.Subtype_h($LS($LZ), _k'#2, a#2, c#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(158,15)"} true;
    }
}



// function declaration for _module._default.ClEnvBelow
function _module.__default.ClEnvBelow($ly: LayerType, c#0: DatatypeType, d#0: DatatypeType) : bool;

function _module.__default.ClEnvBelow#canCall(c#0: DatatypeType, d#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType :: 
  { _module.__default.ClEnvBelow($LS($ly), c#0, d#0) } 
  _module.__default.ClEnvBelow($LS($ly), c#0, d#0)
     == _module.__default.ClEnvBelow($ly, c#0, d#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType :: 
  { _module.__default.ClEnvBelow(AsFuelBottom($ly), c#0, d#0) } 
  _module.__default.ClEnvBelow($ly, c#0, d#0)
     == _module.__default.ClEnvBelow($LZ, c#0, d#0));

// consequence axiom for _module.__default.ClEnvBelow
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType :: 
    { _module.__default.ClEnvBelow($ly, c#0, d#0) } 
    _module.__default.ClEnvBelow#canCall(c#0, d#0)
         || (23 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.ClEnv())
           && $Is(d#0, Tclass._module.ClEnv()))
       ==> true);

function _module.__default.ClEnvBelow#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ClEnvBelow
axiom (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType :: 
  { _module.__default.ClEnvBelow#requires($ly, c#0, d#0) } 
  $Is(c#0, Tclass._module.ClEnv()) && $Is(d#0, Tclass._module.ClEnv())
     ==> _module.__default.ClEnvBelow#requires($ly, c#0, d#0) == true);

// definition axiom for _module.__default.ClEnvBelow (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType :: 
    { _module.__default.ClEnvBelow($LS($ly), c#0, d#0) } 
    _module.__default.ClEnvBelow#canCall(c#0, d#0)
         || (23 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.ClEnv())
           && $Is(d#0, Tclass._module.ClEnv()))
       ==> (forall y#0: Box :: 
          { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#0]): DatatypeType } 
            { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#0]): DatatypeType } 
            { Map#Domain(_module.ClEnv.m(d#0))[y#0] } 
            { Map#Domain(_module.ClEnv.m(c#0))[y#0] } 
          $IsBox(y#0, #$Var)
             ==> _module.ClEnv.ClEnvironment_q(c#0)
               && (Map#Domain(_module.ClEnv.m(c#0))[y#0] ==> _module.ClEnv.ClEnvironment_q(d#0))
               && (
                (Map#Domain(_module.ClEnv.m(c#0))[y#0]
                 ==> Map#Domain(_module.ClEnv.m(d#0))[y#0])
                 ==> _module.ClEnv.ClEnvironment_q(c#0)
                   && (Map#Domain(_module.ClEnv.m(c#0))[y#0]
                     ==> _module.ClEnv.ClEnvironment_q(c#0)
                       && _module.ClEnv.ClEnvironment_q(d#0)
                       && _module.__default.ValBelow#canCall($Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#0]): DatatypeType, 
                        $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#0]): DatatypeType))))
         && _module.__default.ClEnvBelow($LS($ly), c#0, d#0)
           == (forall y#0: Box :: 
            { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#0]): DatatypeType } 
              { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#0]): DatatypeType } 
              { Map#Domain(_module.ClEnv.m(d#0))[y#0] } 
              { Map#Domain(_module.ClEnv.m(c#0))[y#0] } 
            $IsBox(y#0, #$Var)
               ==> (Map#Domain(_module.ClEnv.m(c#0))[y#0]
                   ==> Map#Domain(_module.ClEnv.m(d#0))[y#0])
                 && (Map#Domain(_module.ClEnv.m(c#0))[y#0]
                   ==> _module.__default.ValBelow($ly, 
                    $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#0]): DatatypeType, 
                    $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#0]): DatatypeType))));

// 1st prefix predicate axiom for _module.__default.ClEnvBelow_h
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType :: 
    { _module.__default.ClEnvBelow($LS($ly), c#0, d#0) } 
    $Is(c#0, Tclass._module.ClEnv())
         && $Is(d#0, Tclass._module.ClEnv())
         && _module.__default.ClEnvBelow($LS($ly), c#0, d#0)
       ==> (forall _k#0: int :: 
        { _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0) } 
        LitInt(0) <= _k#0 ==> _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0)));

// 2nd prefix predicate axiom
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType :: 
    { _module.__default.ClEnvBelow($LS($ly), c#0, d#0) } 
    $Is(c#0, Tclass._module.ClEnv())
         && $Is(d#0, Tclass._module.ClEnv())
         && (forall _k#0: int :: 
          { _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0) } 
          LitInt(0) <= _k#0 ==> _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0))
       ==> _module.__default.ClEnvBelow($LS($ly), c#0, d#0));

// 3rd prefix predicate axiom
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, d#0: DatatypeType, _k#0: int :: 
    { _module.__default.ClEnvBelow_h($ly, _k#0, c#0, d#0) } 
    $Is(c#0, Tclass._module.ClEnv())
         && $Is(d#0, Tclass._module.ClEnv())
         && _k#0 == 0
       ==> _module.__default.ClEnvBelow_h($ly, _k#0, c#0, d#0));

procedure CheckWellformed$$_module.__default.ClEnvBelow(c#0: DatatypeType where $Is(c#0, Tclass._module.ClEnv()), 
    d#0: DatatypeType where $Is(d#0, Tclass._module.ClEnv()));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ClEnvBelow(c#0: DatatypeType, d#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#1: Box;
  var ##u#0: DatatypeType;
  var ##v#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ClEnvBelow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(176,19): initial state"} true;
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
        havoc y#1;
        if ($IsBox(y#1, #$Var))
        {
            assume _module.ClEnv.ClEnvironment_q(c#0);
            if (Map#Domain(_module.ClEnv.m(c#0))[y#1])
            {
                assume _module.ClEnv.ClEnvironment_q(d#0);
                if (Map#Domain(_module.ClEnv.m(d#0))[y#1])
                {
                    assume _module.ClEnv.ClEnvironment_q(c#0);
                    assert Map#Domain(_module.ClEnv.m(c#0))[y#1];
                    assume _module.ClEnv.ClEnvironment_q(d#0);
                    assert Map#Domain(_module.ClEnv.m(d#0))[y#1];
                    ##u#0 := $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#1]): DatatypeType;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##u#0, Tclass._module.Val(), $Heap);
                    ##v#0 := $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#1]): DatatypeType;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##v#0, Tclass._module.Val(), $Heap);
                    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.ValBelow#canCall($Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#1]): DatatypeType, 
                      $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#1]): DatatypeType);
                }
            }
        }

        // End Comprehension WF check
        assume _module.__default.ClEnvBelow($LS($LZ), c#0, d#0)
           == (forall y#2: Box :: 
            { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#2]): DatatypeType } 
              { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#2]): DatatypeType } 
              { Map#Domain(_module.ClEnv.m(d#0))[y#2] } 
              { Map#Domain(_module.ClEnv.m(c#0))[y#2] } 
            $IsBox(y#2, #$Var)
               ==> (Map#Domain(_module.ClEnv.m(c#0))[y#2]
                   ==> Map#Domain(_module.ClEnv.m(d#0))[y#2])
                 && (Map#Domain(_module.ClEnv.m(c#0))[y#2]
                   ==> _module.__default.ValBelow($LS($LZ), 
                    $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#2]): DatatypeType, 
                    $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#2]): DatatypeType)));
        assume (forall y#2: Box :: 
          { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#2]): DatatypeType } 
            { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#2]): DatatypeType } 
            { Map#Domain(_module.ClEnv.m(d#0))[y#2] } 
            { Map#Domain(_module.ClEnv.m(c#0))[y#2] } 
          $IsBox(y#2, #$Var)
             ==> _module.ClEnv.ClEnvironment_q(c#0)
               && (Map#Domain(_module.ClEnv.m(c#0))[y#2] ==> _module.ClEnv.ClEnvironment_q(d#0))
               && (
                (Map#Domain(_module.ClEnv.m(c#0))[y#2]
                 ==> Map#Domain(_module.ClEnv.m(d#0))[y#2])
                 ==> _module.ClEnv.ClEnvironment_q(c#0)
                   && (Map#Domain(_module.ClEnv.m(c#0))[y#2]
                     ==> _module.ClEnv.ClEnvironment_q(c#0)
                       && _module.ClEnv.ClEnvironment_q(d#0)
                       && _module.__default.ValBelow#canCall($Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#2]): DatatypeType, 
                        $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#2]): DatatypeType))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ClEnvBelow($LS($LZ), c#0, d#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ClEnvBelow#
function _module.__default.ClEnvBelow_h($ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType) : bool;

function _module.__default.ClEnvBelow_h#canCall(_k#0: int, c#0: DatatypeType, d#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType :: 
  { _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0) } 
  _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0)
     == _module.__default.ClEnvBelow_h($ly, _k#0, c#0, d#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType :: 
  { _module.__default.ClEnvBelow_h(AsFuelBottom($ly), _k#0, c#0, d#0) } 
  _module.__default.ClEnvBelow_h($ly, _k#0, c#0, d#0)
     == _module.__default.ClEnvBelow_h($LZ, _k#0, c#0, d#0));

// consequence axiom for _module.__default.ClEnvBelow_h
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType :: 
    { _module.__default.ClEnvBelow_h($ly, _k#0, c#0, d#0) } 
    _module.__default.ClEnvBelow_h#canCall(_k#0, c#0, d#0)
         || (24 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(c#0, Tclass._module.ClEnv())
           && $Is(d#0, Tclass._module.ClEnv()))
       ==> true);

function _module.__default.ClEnvBelow_h#requires(LayerType, int, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ClEnvBelow_h
axiom (forall $ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType :: 
  { _module.__default.ClEnvBelow_h#requires($ly, _k#0, c#0, d#0) } 
  LitInt(0) <= _k#0
       && $Is(c#0, Tclass._module.ClEnv())
       && $Is(d#0, Tclass._module.ClEnv())
     ==> _module.__default.ClEnvBelow_h#requires($ly, _k#0, c#0, d#0) == true);

// definition axiom for _module.__default.ClEnvBelow_h (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType :: 
    { _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0) } 
    _module.__default.ClEnvBelow_h#canCall(_k#0, c#0, d#0)
         || (24 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(c#0, Tclass._module.ClEnv())
           && $Is(d#0, Tclass._module.ClEnv()))
       ==> (0 < _k#0
           ==> (forall y#3: Box :: 
            { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#3]): DatatypeType } 
              { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#3]): DatatypeType } 
              { Map#Domain(_module.ClEnv.m(d#0))[y#3] } 
              { Map#Domain(_module.ClEnv.m(c#0))[y#3] } 
            $IsBox(y#3, #$Var)
               ==> _module.ClEnv.ClEnvironment_q(c#0)
                 && (Map#Domain(_module.ClEnv.m(c#0))[y#3] ==> _module.ClEnv.ClEnvironment_q(d#0))
                 && (
                  (Map#Domain(_module.ClEnv.m(c#0))[y#3]
                   ==> Map#Domain(_module.ClEnv.m(d#0))[y#3])
                   ==> _module.ClEnv.ClEnvironment_q(c#0)
                     && (Map#Domain(_module.ClEnv.m(c#0))[y#3]
                       ==> _module.ClEnv.ClEnvironment_q(c#0)
                         && _module.ClEnv.ClEnvironment_q(d#0)
                         && _module.__default.ValBelow_h#canCall(_k#0 - 1, 
                          $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#3]): DatatypeType, 
                          $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#3]): DatatypeType)))))
         && _module.__default.ClEnvBelow_h($LS($ly), _k#0, c#0, d#0)
           == (0 < _k#0
             ==> (forall y#3: Box :: 
              { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#3]): DatatypeType } 
                { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#3]): DatatypeType } 
                { Map#Domain(_module.ClEnv.m(d#0))[y#3] } 
                { Map#Domain(_module.ClEnv.m(c#0))[y#3] } 
              $IsBox(y#3, #$Var)
                 ==> (Map#Domain(_module.ClEnv.m(c#0))[y#3]
                     ==> Map#Domain(_module.ClEnv.m(d#0))[y#3])
                   && (Map#Domain(_module.ClEnv.m(c#0))[y#3]
                     ==> _module.__default.ValBelow_h($LS($LZ), 
                      _k#0 - 1, 
                      $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#3]): DatatypeType, 
                      $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#3]): DatatypeType)))));

// definition axiom for _module.__default.ClEnvBelow_h for decreasing-related literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType :: 
    {:weight 3} { _module.__default.ClEnvBelow_h($LS($ly), LitInt(_k#0), c#0, d#0) } 
    _module.__default.ClEnvBelow_h#canCall(LitInt(_k#0), c#0, d#0)
         || (24 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(c#0, Tclass._module.ClEnv())
           && $Is(d#0, Tclass._module.ClEnv()))
       ==> (0 < _k#0
           ==> (forall y#4: Box :: 
            { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#4]): DatatypeType } 
              { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#4]): DatatypeType } 
              { Map#Domain(_module.ClEnv.m(d#0))[y#4] } 
              { Map#Domain(_module.ClEnv.m(c#0))[y#4] } 
            $IsBox(y#4, #$Var)
               ==> _module.ClEnv.ClEnvironment_q(c#0)
                 && (Map#Domain(_module.ClEnv.m(c#0))[y#4] ==> _module.ClEnv.ClEnvironment_q(d#0))
                 && (
                  (Map#Domain(_module.ClEnv.m(c#0))[y#4]
                   ==> Map#Domain(_module.ClEnv.m(d#0))[y#4])
                   ==> _module.ClEnv.ClEnvironment_q(c#0)
                     && (Map#Domain(_module.ClEnv.m(c#0))[y#4]
                       ==> _module.ClEnv.ClEnvironment_q(c#0)
                         && _module.ClEnv.ClEnvironment_q(d#0)
                         && _module.__default.ValBelow_h#canCall(_k#0 - 1, 
                          $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#4]): DatatypeType, 
                          $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#4]): DatatypeType)))))
         && _module.__default.ClEnvBelow_h($LS($ly), LitInt(_k#0), c#0, d#0)
           == (0 < _k#0
             ==> (forall y#4: Box :: 
              { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#4]): DatatypeType } 
                { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#4]): DatatypeType } 
                { Map#Domain(_module.ClEnv.m(d#0))[y#4] } 
                { Map#Domain(_module.ClEnv.m(c#0))[y#4] } 
              $IsBox(y#4, #$Var)
                 ==> (Map#Domain(_module.ClEnv.m(c#0))[y#4]
                     ==> Map#Domain(_module.ClEnv.m(d#0))[y#4])
                   && (Map#Domain(_module.ClEnv.m(c#0))[y#4]
                     ==> _module.__default.ValBelow_h($LS($LZ), 
                      _k#0 - 1, 
                      $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#4]): DatatypeType, 
                      $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#4]): DatatypeType)))));

// definition axiom for _module.__default.ClEnvBelow_h for all literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, c#0: DatatypeType, d#0: DatatypeType :: 
    {:weight 3} { _module.__default.ClEnvBelow_h($LS($ly), LitInt(_k#0), Lit(c#0), Lit(d#0)) } 
    _module.__default.ClEnvBelow_h#canCall(LitInt(_k#0), Lit(c#0), Lit(d#0))
         || (24 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(c#0, Tclass._module.ClEnv())
           && $Is(d#0, Tclass._module.ClEnv()))
       ==> (0 < _k#0
           ==> (forall y#5: Box :: 
            { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#5]): DatatypeType } 
              { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#5]): DatatypeType } 
              { Map#Domain(_module.ClEnv.m(d#0))[y#5] } 
              { Map#Domain(_module.ClEnv.m(c#0))[y#5] } 
            $IsBox(y#5, #$Var)
               ==> _module.ClEnv.ClEnvironment_q(c#0)
                 && (Map#Domain(_module.ClEnv.m(c#0))[y#5] ==> _module.ClEnv.ClEnvironment_q(d#0))
                 && (
                  (Map#Domain(_module.ClEnv.m(c#0))[y#5]
                   ==> Map#Domain(_module.ClEnv.m(d#0))[y#5])
                   ==> _module.ClEnv.ClEnvironment_q(c#0)
                     && (Map#Domain(_module.ClEnv.m(c#0))[y#5]
                       ==> _module.ClEnv.ClEnvironment_q(c#0)
                         && _module.ClEnv.ClEnvironment_q(d#0)
                         && _module.__default.ValBelow_h#canCall(_k#0 - 1, 
                          $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#5]): DatatypeType, 
                          $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#5]): DatatypeType)))))
         && _module.__default.ClEnvBelow_h($LS($ly), LitInt(_k#0), Lit(c#0), Lit(d#0))
           == (0 < _k#0
             ==> (forall y#5: Box :: 
              { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#5]): DatatypeType } 
                { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#5]): DatatypeType } 
                { Map#Domain(_module.ClEnv.m(d#0))[y#5] } 
                { Map#Domain(_module.ClEnv.m(c#0))[y#5] } 
              $IsBox(y#5, #$Var)
                 ==> (Map#Domain(_module.ClEnv.m(c#0))[y#5]
                     ==> Map#Domain(_module.ClEnv.m(d#0))[y#5])
                   && (Map#Domain(_module.ClEnv.m(c#0))[y#5]
                     ==> _module.__default.ValBelow_h($LS($LZ), 
                      _k#0 - 1, 
                      $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#5]): DatatypeType, 
                      $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#5]): DatatypeType)))));

// function declaration for _module._default.ValBelow
function _module.__default.ValBelow($ly: LayerType, u#0: DatatypeType, v#0: DatatypeType) : bool;

function _module.__default.ValBelow#canCall(u#0: DatatypeType, v#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType :: 
  { _module.__default.ValBelow($LS($ly), u#0, v#0) } 
  _module.__default.ValBelow($LS($ly), u#0, v#0)
     == _module.__default.ValBelow($ly, u#0, v#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType :: 
  { _module.__default.ValBelow(AsFuelBottom($ly), u#0, v#0) } 
  _module.__default.ValBelow($ly, u#0, v#0)
     == _module.__default.ValBelow($LZ, u#0, v#0));

// consequence axiom for _module.__default.ValBelow
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType :: 
    { _module.__default.ValBelow($ly, u#0, v#0) } 
    _module.__default.ValBelow#canCall(u#0, v#0)
         || (23 != $FunctionContextHeight
           && 
          $Is(u#0, Tclass._module.Val())
           && $Is(v#0, Tclass._module.Val()))
       ==> true);

function _module.__default.ValBelow#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValBelow
axiom (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType :: 
  { _module.__default.ValBelow#requires($ly, u#0, v#0) } 
  $Is(u#0, Tclass._module.Val()) && $Is(v#0, Tclass._module.Val())
     ==> _module.__default.ValBelow#requires($ly, u#0, v#0) == true);

// definition axiom for _module.__default.ValBelow (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType :: 
    { _module.__default.ValBelow($LS($ly), u#0, v#0) } 
    _module.__default.ValBelow#canCall(u#0, v#0)
         || (23 != $FunctionContextHeight
           && 
          $Is(u#0, Tclass._module.Val())
           && $Is(v#0, Tclass._module.Val()))
       ==> (_module.Val.ValConst_q(u#0)
           ==> 
          _module.Val.ValConst_q(v#0)
           ==> $IsA#_module.Val(u#0) && $IsA#_module.Val(v#0))
         && (!(
            _module.Val.ValConst_q(u#0)
             && _module.Val.ValConst_q(v#0)
             && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
           ==> 
          _module.Val.ValCl_q(u#0)
           ==> 
          _module.Val.ValCl_q(v#0)
           ==> $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(u#0)))
             && $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(v#0)))
             && 
            _module.Cl.Closure_q(_module.Val.cl(u#0))
             && _module.Cl.Closure_q(_module.Val.cl(v#0))
             && (_module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
               ==> _module.Cl.Closure_q(_module.Val.cl(u#0))
                 && _module.Cl.Closure_q(_module.Val.cl(v#0))
                 && _module.__default.ClEnvBelow#canCall(_module.Cl.env(_module.Val.cl(u#0)), _module.Cl.env(_module.Val.cl(v#0)))))
         && _module.__default.ValBelow($LS($ly), u#0, v#0)
           == ((
              _module.Val.ValConst_q(u#0)
               && _module.Val.ValConst_q(v#0)
               && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
             || (
              _module.Val.ValCl_q(u#0)
               && _module.Val.ValCl_q(v#0)
               && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
               && _module.__default.ClEnvBelow($ly, _module.Cl.env(_module.Val.cl(u#0)), _module.Cl.env(_module.Val.cl(v#0))))));

// 1st prefix predicate axiom for _module.__default.ValBelow_h
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType :: 
    { _module.__default.ValBelow($LS($ly), u#0, v#0) } 
    $Is(u#0, Tclass._module.Val())
         && $Is(v#0, Tclass._module.Val())
         && _module.__default.ValBelow($LS($ly), u#0, v#0)
       ==> (forall _k#0: int :: 
        { _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0) } 
        LitInt(0) <= _k#0 ==> _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0)));

// 2nd prefix predicate axiom
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType :: 
    { _module.__default.ValBelow($LS($ly), u#0, v#0) } 
    $Is(u#0, Tclass._module.Val())
         && $Is(v#0, Tclass._module.Val())
         && (forall _k#0: int :: 
          { _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0) } 
          LitInt(0) <= _k#0 ==> _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0))
       ==> _module.__default.ValBelow($LS($ly), u#0, v#0));

// 3rd prefix predicate axiom
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, u#0: DatatypeType, v#0: DatatypeType, _k#0: int :: 
    { _module.__default.ValBelow_h($ly, _k#0, u#0, v#0) } 
    $Is(u#0, Tclass._module.Val()) && $Is(v#0, Tclass._module.Val()) && _k#0 == 0
       ==> _module.__default.ValBelow_h($ly, _k#0, u#0, v#0));

procedure CheckWellformed$$_module.__default.ValBelow(u#0: DatatypeType where $Is(u#0, Tclass._module.Val()), 
    v#0: DatatypeType where $Is(v#0, Tclass._module.Val()));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ValBelow(u#0: DatatypeType, v#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: DatatypeType;
  var ##d#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ValBelow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(182,19): initial state"} true;
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
        if (_module.Val.ValConst_q(u#0))
        {
        }

        if (_module.Val.ValConst_q(u#0) && _module.Val.ValConst_q(v#0))
        {
        }

        if (!(
          _module.Val.ValConst_q(u#0)
           && _module.Val.ValConst_q(v#0)
           && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0)))
        {
            if (_module.Val.ValCl_q(u#0))
            {
            }

            if (_module.Val.ValCl_q(u#0) && _module.Val.ValCl_q(v#0))
            {
                assert _module.Val.ValCl_q(u#0);
                assume _module.Cl.Closure_q(_module.Val.cl(u#0));
                assert _module.Val.ValCl_q(v#0);
                assume _module.Cl.Closure_q(_module.Val.cl(v#0));
            }

            if (_module.Val.ValCl_q(u#0)
               && _module.Val.ValCl_q(v#0)
               && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0))))
            {
                assert _module.Val.ValCl_q(u#0);
                assume _module.Cl.Closure_q(_module.Val.cl(u#0));
                assert _module.Val.ValCl_q(v#0);
                assume _module.Cl.Closure_q(_module.Val.cl(v#0));
                ##c#0 := _module.Cl.env(_module.Val.cl(u#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#0, Tclass._module.ClEnv(), $Heap);
                ##d#0 := _module.Cl.env(_module.Val.cl(v#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##d#0, Tclass._module.ClEnv(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.ClEnvBelow#canCall(_module.Cl.env(_module.Val.cl(u#0)), _module.Cl.env(_module.Val.cl(v#0)));
            }
        }

        assume _module.__default.ValBelow($LS($LZ), u#0, v#0)
           == ((
              _module.Val.ValConst_q(u#0)
               && _module.Val.ValConst_q(v#0)
               && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
             || (
              _module.Val.ValCl_q(u#0)
               && _module.Val.ValCl_q(v#0)
               && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
               && _module.__default.ClEnvBelow($LS($LZ), 
                _module.Cl.env(_module.Val.cl(u#0)), 
                _module.Cl.env(_module.Val.cl(v#0)))));
        assume (_module.Val.ValConst_q(u#0)
             ==> 
            _module.Val.ValConst_q(v#0)
             ==> $IsA#_module.Val(u#0) && $IsA#_module.Val(v#0))
           && (!(
              _module.Val.ValConst_q(u#0)
               && _module.Val.ValConst_q(v#0)
               && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
             ==> 
            _module.Val.ValCl_q(u#0)
             ==> 
            _module.Val.ValCl_q(v#0)
             ==> $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(u#0)))
               && $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(v#0)))
               && 
              _module.Cl.Closure_q(_module.Val.cl(u#0))
               && _module.Cl.Closure_q(_module.Val.cl(v#0))
               && (_module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
                 ==> _module.Cl.Closure_q(_module.Val.cl(u#0))
                   && _module.Cl.Closure_q(_module.Val.cl(v#0))
                   && _module.__default.ClEnvBelow#canCall(_module.Cl.env(_module.Val.cl(u#0)), _module.Cl.env(_module.Val.cl(v#0)))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ValBelow($LS($LZ), u#0, v#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ValBelow#
function _module.__default.ValBelow_h($ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType) : bool;

function _module.__default.ValBelow_h#canCall(_k#0: int, u#0: DatatypeType, v#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType :: 
  { _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0) } 
  _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0)
     == _module.__default.ValBelow_h($ly, _k#0, u#0, v#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType :: 
  { _module.__default.ValBelow_h(AsFuelBottom($ly), _k#0, u#0, v#0) } 
  _module.__default.ValBelow_h($ly, _k#0, u#0, v#0)
     == _module.__default.ValBelow_h($LZ, _k#0, u#0, v#0));

// consequence axiom for _module.__default.ValBelow_h
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType :: 
    { _module.__default.ValBelow_h($ly, _k#0, u#0, v#0) } 
    _module.__default.ValBelow_h#canCall(_k#0, u#0, v#0)
         || (25 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(u#0, Tclass._module.Val())
           && $Is(v#0, Tclass._module.Val()))
       ==> true);

function _module.__default.ValBelow_h#requires(LayerType, int, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValBelow_h
axiom (forall $ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType :: 
  { _module.__default.ValBelow_h#requires($ly, _k#0, u#0, v#0) } 
  LitInt(0) <= _k#0
       && $Is(u#0, Tclass._module.Val())
       && $Is(v#0, Tclass._module.Val())
     ==> _module.__default.ValBelow_h#requires($ly, _k#0, u#0, v#0) == true);

// definition axiom for _module.__default.ValBelow_h (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType :: 
    { _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0) } 
    _module.__default.ValBelow_h#canCall(_k#0, u#0, v#0)
         || (25 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(u#0, Tclass._module.Val())
           && $Is(v#0, Tclass._module.Val()))
       ==> (0 < _k#0
           ==> (_module.Val.ValConst_q(u#0)
               ==> 
              _module.Val.ValConst_q(v#0)
               ==> $IsA#_module.Val(u#0) && $IsA#_module.Val(v#0))
             && (!(
                _module.Val.ValConst_q(u#0)
                 && _module.Val.ValConst_q(v#0)
                 && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
               ==> 
              _module.Val.ValCl_q(u#0)
               ==> 
              _module.Val.ValCl_q(v#0)
               ==> $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(u#0)))
                 && $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(v#0)))
                 && 
                _module.Cl.Closure_q(_module.Val.cl(u#0))
                 && _module.Cl.Closure_q(_module.Val.cl(v#0))
                 && (_module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
                   ==> _module.Cl.Closure_q(_module.Val.cl(u#0))
                     && _module.Cl.Closure_q(_module.Val.cl(v#0))
                     && _module.__default.ClEnvBelow_h#canCall(_k#0 - 1, 
                      _module.Cl.env(_module.Val.cl(u#0)), 
                      _module.Cl.env(_module.Val.cl(v#0))))))
         && _module.__default.ValBelow_h($LS($ly), _k#0, u#0, v#0)
           == (0 < _k#0
             ==> (
                _module.Val.ValConst_q(u#0)
                 && _module.Val.ValConst_q(v#0)
                 && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
               || (
                _module.Val.ValCl_q(u#0)
                 && _module.Val.ValCl_q(v#0)
                 && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
                 && _module.__default.ClEnvBelow_h($LS($LZ), 
                  _k#0 - 1, 
                  _module.Cl.env(_module.Val.cl(u#0)), 
                  _module.Cl.env(_module.Val.cl(v#0))))));

// definition axiom for _module.__default.ValBelow_h for decreasing-related literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValBelow_h($LS($ly), LitInt(_k#0), u#0, v#0) } 
    _module.__default.ValBelow_h#canCall(LitInt(_k#0), u#0, v#0)
         || (25 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(u#0, Tclass._module.Val())
           && $Is(v#0, Tclass._module.Val()))
       ==> (0 < _k#0
           ==> (_module.Val.ValConst_q(u#0)
               ==> 
              _module.Val.ValConst_q(v#0)
               ==> $IsA#_module.Val(u#0) && $IsA#_module.Val(v#0))
             && (!(
                _module.Val.ValConst_q(u#0)
                 && _module.Val.ValConst_q(v#0)
                 && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
               ==> 
              _module.Val.ValCl_q(u#0)
               ==> 
              _module.Val.ValCl_q(v#0)
               ==> $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(u#0)))
                 && $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(v#0)))
                 && 
                _module.Cl.Closure_q(_module.Val.cl(u#0))
                 && _module.Cl.Closure_q(_module.Val.cl(v#0))
                 && (_module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
                   ==> _module.Cl.Closure_q(_module.Val.cl(u#0))
                     && _module.Cl.Closure_q(_module.Val.cl(v#0))
                     && _module.__default.ClEnvBelow_h#canCall(_k#0 - 1, 
                      _module.Cl.env(_module.Val.cl(u#0)), 
                      _module.Cl.env(_module.Val.cl(v#0))))))
         && _module.__default.ValBelow_h($LS($ly), LitInt(_k#0), u#0, v#0)
           == (0 < _k#0
             ==> (
                _module.Val.ValConst_q(u#0)
                 && _module.Val.ValConst_q(v#0)
                 && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
               || (
                _module.Val.ValCl_q(u#0)
                 && _module.Val.ValCl_q(v#0)
                 && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
                 && _module.__default.ClEnvBelow_h($LS($LZ), 
                  _k#0 - 1, 
                  _module.Cl.env(_module.Val.cl(u#0)), 
                  _module.Cl.env(_module.Val.cl(v#0))))));

// definition axiom for _module.__default.ValBelow_h for all literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: int, u#0: DatatypeType, v#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValBelow_h($LS($ly), LitInt(_k#0), Lit(u#0), Lit(v#0)) } 
    _module.__default.ValBelow_h#canCall(LitInt(_k#0), Lit(u#0), Lit(v#0))
         || (25 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(u#0, Tclass._module.Val())
           && $Is(v#0, Tclass._module.Val()))
       ==> (0 < _k#0
           ==> (_module.Val.ValConst_q(u#0)
               ==> 
              _module.Val.ValConst_q(v#0)
               ==> $IsA#_module.Val(u#0) && $IsA#_module.Val(v#0))
             && (!(
                _module.Val.ValConst_q(u#0)
                 && _module.Val.ValConst_q(v#0)
                 && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
               ==> 
              _module.Val.ValCl_q(u#0)
               ==> 
              _module.Val.ValCl_q(v#0)
               ==> $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(u#0)))
                 && $IsA#_module.LambdaAbs(_module.Cl.abs(_module.Val.cl(v#0)))
                 && 
                _module.Cl.Closure_q(_module.Val.cl(u#0))
                 && _module.Cl.Closure_q(_module.Val.cl(v#0))
                 && (_module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
                   ==> _module.Cl.Closure_q(_module.Val.cl(u#0))
                     && _module.Cl.Closure_q(_module.Val.cl(v#0))
                     && _module.__default.ClEnvBelow_h#canCall(_k#0 - 1, 
                      _module.Cl.env(_module.Val.cl(u#0)), 
                      _module.Cl.env(_module.Val.cl(v#0))))))
         && _module.__default.ValBelow_h($LS($ly), LitInt(_k#0), Lit(u#0), Lit(v#0))
           == (0 < _k#0
             ==> (
                _module.Val.ValConst_q(u#0)
                 && _module.Val.ValConst_q(v#0)
                 && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
               || (
                _module.Val.ValCl_q(u#0)
                 && _module.Val.ValCl_q(v#0)
                 && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
                 && _module.__default.ClEnvBelow_h($LS($LZ), 
                  _k#0 - 1, 
                  _module.Cl.env(_module.Val.cl(u#0)), 
                  _module.Cl.env(_module.Val.cl(v#0))))));

procedure CheckWellformed$$_module.__default.Theorem4a__ClEnvBelow__Is__Transitive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.ClEnv())
         && $IsAlloc(c#0, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(c#0), 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.ClEnv())
         && $IsAlloc(d#0, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(d#0), 
    e#0: DatatypeType
       where $Is(e#0, Tclass._module.ClEnv())
         && $IsAlloc(e#0, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(e#0));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem4a__ClEnvBelow__Is__Transitive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.ClEnv())
         && $IsAlloc(c#0, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(c#0), 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.ClEnv())
         && $IsAlloc(d#0, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(d#0), 
    e#0: DatatypeType
       where $Is(e#0, Tclass._module.ClEnv())
         && $IsAlloc(e#0, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(e#0));
  // user-defined preconditions
  requires _module.__default.ClEnvBelow#canCall(c#0, d#0)
     ==> _module.__default.ClEnvBelow($LS($LZ), c#0, d#0)
       || (forall y#0: Box :: 
        { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#0]): DatatypeType } 
          { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#0]): DatatypeType } 
          { Map#Domain(_module.ClEnv.m(d#0))[y#0] } 
          { Map#Domain(_module.ClEnv.m(c#0))[y#0] } 
        $IsBox(y#0, #$Var)
           ==> (Map#Domain(_module.ClEnv.m(c#0))[y#0]
               ==> Map#Domain(_module.ClEnv.m(d#0))[y#0])
             && (Map#Domain(_module.ClEnv.m(c#0))[y#0]
               ==> _module.__default.ValBelow($LS($LS($LZ)), 
                $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#0]): DatatypeType, 
                $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#0]): DatatypeType)));
  requires _module.__default.ClEnvBelow#canCall(d#0, e#0)
     ==> _module.__default.ClEnvBelow($LS($LZ), d#0, e#0)
       || (forall y#1: Box :: 
        { $Unbox(Map#Elements(_module.ClEnv.m(e#0))[y#1]): DatatypeType } 
          { $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#1]): DatatypeType } 
          { Map#Domain(_module.ClEnv.m(e#0))[y#1] } 
          { Map#Domain(_module.ClEnv.m(d#0))[y#1] } 
        $IsBox(y#1, #$Var)
           ==> (Map#Domain(_module.ClEnv.m(d#0))[y#1]
               ==> Map#Domain(_module.ClEnv.m(e#0))[y#1])
             && (Map#Domain(_module.ClEnv.m(d#0))[y#1]
               ==> _module.__default.ValBelow($LS($LS($LZ)), 
                $Unbox(Map#Elements(_module.ClEnv.m(d#0))[y#1]): DatatypeType, 
                $Unbox(Map#Elements(_module.ClEnv.m(e#0))[y#1]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ClEnvBelow#canCall(c#0, e#0);
  free ensures _module.__default.ClEnvBelow#canCall(c#0, e#0)
     && 
    _module.__default.ClEnvBelow($LS($LZ), c#0, e#0)
     && (forall y#2: Box :: 
      { $Unbox(Map#Elements(_module.ClEnv.m(e#0))[y#2]): DatatypeType } 
        { $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#2]): DatatypeType } 
        { Map#Domain(_module.ClEnv.m(e#0))[y#2] } 
        { Map#Domain(_module.ClEnv.m(c#0))[y#2] } 
      $IsBox(y#2, #$Var)
         ==> (Map#Domain(_module.ClEnv.m(c#0))[y#2]
             ==> Map#Domain(_module.ClEnv.m(e#0))[y#2])
           && (Map#Domain(_module.ClEnv.m(c#0))[y#2]
             ==> _module.__default.ValBelow($LS($LZ), 
              $Unbox(Map#Elements(_module.ClEnv.m(c#0))[y#2]): DatatypeType, 
              $Unbox(Map#Elements(_module.ClEnv.m(e#0))[y#2]): DatatypeType)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, d#1, e#1} CoCall$$_module.__default.Theorem4a__ClEnvBelow__Is__Transitive_h(_k#0: int where LitInt(0) <= _k#0, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.ClEnv())
         && $IsAlloc(c#1, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(c#1), 
    d#1: DatatypeType
       where $Is(d#1, Tclass._module.ClEnv())
         && $IsAlloc(d#1, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(d#1), 
    e#1: DatatypeType
       where $Is(e#1, Tclass._module.ClEnv())
         && $IsAlloc(e#1, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(e#1));
  // user-defined preconditions
  requires _module.__default.ClEnvBelow#canCall(c#1, d#1)
     ==> _module.__default.ClEnvBelow($LS($LZ), c#1, d#1)
       || (forall y#3: Box :: 
        { $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#3]): DatatypeType } 
          { $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#3]): DatatypeType } 
          { Map#Domain(_module.ClEnv.m(d#1))[y#3] } 
          { Map#Domain(_module.ClEnv.m(c#1))[y#3] } 
        $IsBox(y#3, #$Var)
           ==> (Map#Domain(_module.ClEnv.m(c#1))[y#3]
               ==> Map#Domain(_module.ClEnv.m(d#1))[y#3])
             && (Map#Domain(_module.ClEnv.m(c#1))[y#3]
               ==> _module.__default.ValBelow($LS($LS($LZ)), 
                $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#3]): DatatypeType, 
                $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#3]): DatatypeType)));
  requires _module.__default.ClEnvBelow#canCall(d#1, e#1)
     ==> _module.__default.ClEnvBelow($LS($LZ), d#1, e#1)
       || (forall y#4: Box :: 
        { $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#4]): DatatypeType } 
          { $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#4]): DatatypeType } 
          { Map#Domain(_module.ClEnv.m(e#1))[y#4] } 
          { Map#Domain(_module.ClEnv.m(d#1))[y#4] } 
        $IsBox(y#4, #$Var)
           ==> (Map#Domain(_module.ClEnv.m(d#1))[y#4]
               ==> Map#Domain(_module.ClEnv.m(e#1))[y#4])
             && (Map#Domain(_module.ClEnv.m(d#1))[y#4]
               ==> _module.__default.ValBelow($LS($LS($LZ)), 
                $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#4]): DatatypeType, 
                $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#4]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ClEnvBelow_h#canCall(_k#0, c#1, e#1);
  free ensures _module.__default.ClEnvBelow_h#canCall(_k#0, c#1, e#1)
     && 
    _module.__default.ClEnvBelow_h($LS($LZ), _k#0, c#1, e#1)
     && (0 < _k#0
       ==> (forall y#5: Box :: 
        { $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#5]): DatatypeType } 
          { $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#5]): DatatypeType } 
          { Map#Domain(_module.ClEnv.m(e#1))[y#5] } 
          { Map#Domain(_module.ClEnv.m(c#1))[y#5] } 
        $IsBox(y#5, #$Var)
           ==> (Map#Domain(_module.ClEnv.m(c#1))[y#5]
               ==> Map#Domain(_module.ClEnv.m(e#1))[y#5])
             && (Map#Domain(_module.ClEnv.m(c#1))[y#5]
               ==> _module.__default.ValBelow_h($LS($LZ), 
                _k#0 - 1, 
                $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#5]): DatatypeType, 
                $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#5]): DatatypeType))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, d#1, e#1} Impl$$_module.__default.Theorem4a__ClEnvBelow__Is__Transitive_h(_k#0: int where LitInt(0) <= _k#0, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.ClEnv())
         && $IsAlloc(c#1, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(c#1), 
    d#1: DatatypeType
       where $Is(d#1, Tclass._module.ClEnv())
         && $IsAlloc(d#1, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(d#1), 
    e#1: DatatypeType
       where $Is(e#1, Tclass._module.ClEnv())
         && $IsAlloc(e#1, Tclass._module.ClEnv(), $Heap)
         && $IsA#_module.ClEnv(e#1))
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.ClEnvBelow#canCall(c#1, d#1)
     && 
    _module.__default.ClEnvBelow($LS($LZ), c#1, d#1)
     && (forall y#6: Box :: 
      { $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#6]): DatatypeType } 
        { $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#6]): DatatypeType } 
        { Map#Domain(_module.ClEnv.m(d#1))[y#6] } 
        { Map#Domain(_module.ClEnv.m(c#1))[y#6] } 
      $IsBox(y#6, #$Var)
         ==> (Map#Domain(_module.ClEnv.m(c#1))[y#6]
             ==> Map#Domain(_module.ClEnv.m(d#1))[y#6])
           && (Map#Domain(_module.ClEnv.m(c#1))[y#6]
             ==> _module.__default.ValBelow($LS($LZ), 
              $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#6]): DatatypeType, 
              $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#6]): DatatypeType)));
  free requires _module.__default.ClEnvBelow#canCall(d#1, e#1)
     && 
    _module.__default.ClEnvBelow($LS($LZ), d#1, e#1)
     && (forall y#7: Box :: 
      { $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#7]): DatatypeType } 
        { $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#7]): DatatypeType } 
        { Map#Domain(_module.ClEnv.m(e#1))[y#7] } 
        { Map#Domain(_module.ClEnv.m(d#1))[y#7] } 
      $IsBox(y#7, #$Var)
         ==> (Map#Domain(_module.ClEnv.m(d#1))[y#7]
             ==> Map#Domain(_module.ClEnv.m(e#1))[y#7])
           && (Map#Domain(_module.ClEnv.m(d#1))[y#7]
             ==> _module.__default.ValBelow($LS($LZ), 
              $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#7]): DatatypeType, 
              $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#7]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ClEnvBelow_h#canCall(_k#0, c#1, e#1);
  ensures _module.__default.ClEnvBelow_h#canCall(_k#0, c#1, e#1)
     ==> _module.__default.ClEnvBelow_h($LS($LZ), _k#0, c#1, e#1)
       || (0 < _k#0
         ==> (forall y#8: Box :: 
          { $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#8]): DatatypeType } 
            { $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#8]): DatatypeType } 
            { Map#Domain(_module.ClEnv.m(e#1))[y#8] } 
            { Map#Domain(_module.ClEnv.m(c#1))[y#8] } 
          $IsBox(y#8, #$Var)
             ==> (Map#Domain(_module.ClEnv.m(c#1))[y#8]
                 ==> Map#Domain(_module.ClEnv.m(e#1))[y#8])
               && (Map#Domain(_module.ClEnv.m(c#1))[y#8]
                 ==> _module.__default.ValBelow_h($LS($LS($LZ)), 
                  _k#0 - 1, 
                  $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#8]): DatatypeType, 
                  $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#8]): DatatypeType))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, c#1, d#1, e#1} Impl$$_module.__default.Theorem4a__ClEnvBelow__Is__Transitive_h(_k#0: int, c#1: DatatypeType, d#1: DatatypeType, e#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var y#9: Box;
  var _k##0: int;
  var u##0: DatatypeType;
  var v##0: DatatypeType;
  var w##0: DatatypeType;
  var $initHeapForallStmt#0_0: Heap;

    // AddMethodImpl: Theorem4a_ClEnvBelow_Is_Transitive#, Impl$$_module.__default.Theorem4a__ClEnvBelow__Is__Transitive_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(188,15): initial state"} true;
    assume $IsA#_module.ClEnv(c#1);
    assume $IsA#_module.ClEnv(d#1);
    assume $IsA#_module.ClEnv(e#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, 
        $ih#c0#0: DatatypeType, 
        $ih#d0#0: DatatypeType, 
        $ih#e0#0: DatatypeType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#c0#0, Tclass._module.ClEnv())
           && $Is($ih#d0#0, Tclass._module.ClEnv())
           && $Is($ih#e0#0, Tclass._module.ClEnv())
           && 
          _module.__default.ClEnvBelow($LS($LZ), $ih#c0#0, $ih#d0#0)
           && _module.__default.ClEnvBelow($LS($LZ), $ih#d0#0, $ih#e0#0)
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.ClEnvBelow_h($LS($LZ), $ih#_k0#0, $ih#c0#0, $ih#e0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(191,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(192,3)
        if (*)
        {
            // Assume Fuel Constant
            havoc y#9;
            assume $IsBox(y#9, #$Var);
            assume _module.ClEnv.ClEnvironment_q(c#1);
            assume _module.ClEnv.ClEnvironment_q(c#1);
            assume Map#Domain(_module.ClEnv.m(c#1))[y#9];
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(193,44)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(_k#0 - 1, Tclass._System.nat());
            _k##0 := _k#0 - 1;
            assume _module.ClEnv.ClEnvironment_q(c#1);
            assert Map#Domain(_module.ClEnv.m(c#1))[y#9];
            assume _module.ClEnv.ClEnvironment_q(c#1);
            // ProcessCallStmt: CheckSubrange
            u##0 := $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#9]): DatatypeType;
            assume _module.ClEnv.ClEnvironment_q(d#1);
            assert Map#Domain(_module.ClEnv.m(d#1))[y#9];
            assume _module.ClEnv.ClEnvironment_q(d#1);
            // ProcessCallStmt: CheckSubrange
            v##0 := $Unbox(Map#Elements(_module.ClEnv.m(d#1))[y#9]): DatatypeType;
            assume _module.ClEnv.ClEnvironment_q(e#1);
            assert Map#Domain(_module.ClEnv.m(e#1))[y#9];
            assume _module.ClEnv.ClEnvironment_q(e#1);
            // ProcessCallStmt: CheckSubrange
            w##0 := $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#9]): DatatypeType;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= _k#0 || _k##0 == _k#0;
            assert _k##0 < _k#0;
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem4b__ValBelow__Is__Transitive_h(_k##0, u##0, v##0, w##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(193,67)"} true;
            assume false;
        }
        else
        {
            $initHeapForallStmt#0_0 := $Heap;
            havoc $Heap, $Tick;
            assume (forall $o: ref :: 
              { $Heap[$o] } 
              $o != null && read($initHeapForallStmt#0_0, $o, alloc)
                 ==> $Heap[$o] == $initHeapForallStmt#0_0[$o]);
            assume $HeapSucc($initHeapForallStmt#0_0, $Heap);
            assume (forall y#10: Box :: 
              $IsBox(y#10, #$Var) && Map#Domain(_module.ClEnv.m(c#1))[y#10]
                 ==> _module.__default.ValBelow_h($LS($LZ), 
                  _k#0 - 1, 
                  $Unbox(Map#Elements(_module.ClEnv.m(c#1))[y#10]): DatatypeType, 
                  $Unbox(Map#Elements(_module.ClEnv.m(e#1))[y#10]): DatatypeType));
        }

        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(194,2)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.Theorem4b__ValBelow__Is__Transitive(u#0: DatatypeType
       where $Is(u#0, Tclass._module.Val())
         && $IsAlloc(u#0, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(u#0), 
    v#0: DatatypeType
       where $Is(v#0, Tclass._module.Val())
         && $IsAlloc(v#0, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(v#0), 
    w#0: DatatypeType
       where $Is(w#0, Tclass._module.Val())
         && $IsAlloc(w#0, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(w#0));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem4b__ValBelow__Is__Transitive(u#0: DatatypeType
       where $Is(u#0, Tclass._module.Val())
         && $IsAlloc(u#0, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(u#0), 
    v#0: DatatypeType
       where $Is(v#0, Tclass._module.Val())
         && $IsAlloc(v#0, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(v#0), 
    w#0: DatatypeType
       where $Is(w#0, Tclass._module.Val())
         && $IsAlloc(w#0, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(w#0));
  // user-defined preconditions
  requires _module.__default.ValBelow#canCall(u#0, v#0)
     ==> _module.__default.ValBelow($LS($LZ), u#0, v#0)
       || 
      (
        _module.Val.ValConst_q(u#0)
         && _module.Val.ValConst_q(v#0)
         && $Eq#_module.Val($LS($LS($LZ)), u#0, v#0))
       || (
        _module.Val.ValCl_q(u#0)
         && _module.Val.ValCl_q(v#0)
         && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(v#0)))
         && _module.__default.ClEnvBelow($LS($LS($LZ)), 
          _module.Cl.env(_module.Val.cl(u#0)), 
          _module.Cl.env(_module.Val.cl(v#0))));
  requires _module.__default.ValBelow#canCall(v#0, w#0)
     ==> _module.__default.ValBelow($LS($LZ), v#0, w#0)
       || 
      (
        _module.Val.ValConst_q(v#0)
         && _module.Val.ValConst_q(w#0)
         && $Eq#_module.Val($LS($LS($LZ)), v#0, w#0))
       || (
        _module.Val.ValCl_q(v#0)
         && _module.Val.ValCl_q(w#0)
         && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(v#0)), _module.Cl.abs(_module.Val.cl(w#0)))
         && _module.__default.ClEnvBelow($LS($LS($LZ)), 
          _module.Cl.env(_module.Val.cl(v#0)), 
          _module.Cl.env(_module.Val.cl(w#0))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValBelow#canCall(u#0, w#0);
  free ensures _module.__default.ValBelow#canCall(u#0, w#0)
     && 
    _module.__default.ValBelow($LS($LZ), u#0, w#0)
     && ((
        _module.Val.ValConst_q(u#0)
         && _module.Val.ValConst_q(w#0)
         && $Eq#_module.Val($LS($LS($LZ)), u#0, w#0))
       || (
        _module.Val.ValCl_q(u#0)
         && _module.Val.ValCl_q(w#0)
         && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#0)), _module.Cl.abs(_module.Val.cl(w#0)))
         && _module.__default.ClEnvBelow($LS($LZ), 
          _module.Cl.env(_module.Val.cl(u#0)), 
          _module.Cl.env(_module.Val.cl(w#0)))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, u#1, v#1, w#1} CoCall$$_module.__default.Theorem4b__ValBelow__Is__Transitive_h(_k#0: int where LitInt(0) <= _k#0, 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Val())
         && $IsAlloc(u#1, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(u#1), 
    v#1: DatatypeType
       where $Is(v#1, Tclass._module.Val())
         && $IsAlloc(v#1, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(v#1), 
    w#1: DatatypeType
       where $Is(w#1, Tclass._module.Val())
         && $IsAlloc(w#1, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(w#1));
  // user-defined preconditions
  requires _module.__default.ValBelow#canCall(u#1, v#1)
     ==> _module.__default.ValBelow($LS($LZ), u#1, v#1)
       || 
      (
        _module.Val.ValConst_q(u#1)
         && _module.Val.ValConst_q(v#1)
         && $Eq#_module.Val($LS($LS($LZ)), u#1, v#1))
       || (
        _module.Val.ValCl_q(u#1)
         && _module.Val.ValCl_q(v#1)
         && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#1)), _module.Cl.abs(_module.Val.cl(v#1)))
         && _module.__default.ClEnvBelow($LS($LS($LZ)), 
          _module.Cl.env(_module.Val.cl(u#1)), 
          _module.Cl.env(_module.Val.cl(v#1))));
  requires _module.__default.ValBelow#canCall(v#1, w#1)
     ==> _module.__default.ValBelow($LS($LZ), v#1, w#1)
       || 
      (
        _module.Val.ValConst_q(v#1)
         && _module.Val.ValConst_q(w#1)
         && $Eq#_module.Val($LS($LS($LZ)), v#1, w#1))
       || (
        _module.Val.ValCl_q(v#1)
         && _module.Val.ValCl_q(w#1)
         && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(v#1)), _module.Cl.abs(_module.Val.cl(w#1)))
         && _module.__default.ClEnvBelow($LS($LS($LZ)), 
          _module.Cl.env(_module.Val.cl(v#1)), 
          _module.Cl.env(_module.Val.cl(w#1))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValBelow_h#canCall(_k#0, u#1, w#1);
  free ensures _module.__default.ValBelow_h#canCall(_k#0, u#1, w#1)
     && 
    _module.__default.ValBelow_h($LS($LZ), _k#0, u#1, w#1)
     && (0 < _k#0
       ==> (
          _module.Val.ValConst_q(u#1)
           && _module.Val.ValConst_q(w#1)
           && $Eq#_module.Val($LS($LS($LZ)), u#1, w#1))
         || (
          _module.Val.ValCl_q(u#1)
           && _module.Val.ValCl_q(w#1)
           && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#1)), _module.Cl.abs(_module.Val.cl(w#1)))
           && _module.__default.ClEnvBelow_h($LS($LZ), 
            _k#0 - 1, 
            _module.Cl.env(_module.Val.cl(u#1)), 
            _module.Cl.env(_module.Val.cl(w#1)))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, u#1, v#1, w#1} Impl$$_module.__default.Theorem4b__ValBelow__Is__Transitive_h(_k#0: int where LitInt(0) <= _k#0, 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Val())
         && $IsAlloc(u#1, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(u#1), 
    v#1: DatatypeType
       where $Is(v#1, Tclass._module.Val())
         && $IsAlloc(v#1, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(v#1), 
    w#1: DatatypeType
       where $Is(w#1, Tclass._module.Val())
         && $IsAlloc(w#1, Tclass._module.Val(), $Heap)
         && $IsA#_module.Val(w#1))
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.ValBelow#canCall(u#1, v#1)
     && 
    _module.__default.ValBelow($LS($LZ), u#1, v#1)
     && ((
        _module.Val.ValConst_q(u#1)
         && _module.Val.ValConst_q(v#1)
         && $Eq#_module.Val($LS($LS($LZ)), u#1, v#1))
       || (
        _module.Val.ValCl_q(u#1)
         && _module.Val.ValCl_q(v#1)
         && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#1)), _module.Cl.abs(_module.Val.cl(v#1)))
         && _module.__default.ClEnvBelow($LS($LZ), 
          _module.Cl.env(_module.Val.cl(u#1)), 
          _module.Cl.env(_module.Val.cl(v#1)))));
  free requires _module.__default.ValBelow#canCall(v#1, w#1)
     && 
    _module.__default.ValBelow($LS($LZ), v#1, w#1)
     && ((
        _module.Val.ValConst_q(v#1)
         && _module.Val.ValConst_q(w#1)
         && $Eq#_module.Val($LS($LS($LZ)), v#1, w#1))
       || (
        _module.Val.ValCl_q(v#1)
         && _module.Val.ValCl_q(w#1)
         && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(v#1)), _module.Cl.abs(_module.Val.cl(w#1)))
         && _module.__default.ClEnvBelow($LS($LZ), 
          _module.Cl.env(_module.Val.cl(v#1)), 
          _module.Cl.env(_module.Val.cl(w#1)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValBelow_h#canCall(_k#0, u#1, w#1);
  ensures _module.__default.ValBelow_h#canCall(_k#0, u#1, w#1)
     ==> _module.__default.ValBelow_h($LS($LZ), _k#0, u#1, w#1)
       || (0 < _k#0
         ==> (
            _module.Val.ValConst_q(u#1)
             && _module.Val.ValConst_q(w#1)
             && $Eq#_module.Val($LS($LS($LZ)), u#1, w#1))
           || (
            _module.Val.ValCl_q(u#1)
             && _module.Val.ValCl_q(w#1)
             && _module.LambdaAbs#Equal(_module.Cl.abs(_module.Val.cl(u#1)), _module.Cl.abs(_module.Val.cl(w#1)))
             && _module.__default.ClEnvBelow_h($LS($LS($LZ)), 
              _k#0 - 1, 
              _module.Cl.env(_module.Val.cl(u#1)), 
              _module.Cl.env(_module.Val.cl(w#1)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, u#1, v#1, w#1} Impl$$_module.__default.Theorem4b__ValBelow__Is__Transitive_h(_k#0: int, u#1: DatatypeType, v#1: DatatypeType, w#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: int;
  var c##0: DatatypeType;
  var d##0: DatatypeType;
  var e##0: DatatypeType;

    // AddMethodImpl: Theorem4b_ValBelow_Is_Transitive#, Impl$$_module.__default.Theorem4b__ValBelow__Is__Transitive_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(196,15): initial state"} true;
    assume $IsA#_module.Val(u#1);
    assume $IsA#_module.Val(v#1);
    assume $IsA#_module.Val(w#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, 
        $ih#u0#0: DatatypeType, 
        $ih#v0#0: DatatypeType, 
        $ih#w0#0: DatatypeType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#u0#0, Tclass._module.Val())
           && $Is($ih#v0#0, Tclass._module.Val())
           && $Is($ih#w0#0, Tclass._module.Val())
           && 
          _module.__default.ValBelow($LS($LZ), $ih#u0#0, $ih#v0#0)
           && _module.__default.ValBelow($LS($LZ), $ih#v0#0, $ih#w0#0)
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.ValBelow_h($LS($LZ), $ih#_k0#0, $ih#u0#0, $ih#w0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(199,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(200,3)
        assume true;
        if (_module.Val.ValCl_q(u#1))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(201,39)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(_k#0 - 1, Tclass._System.nat());
            _k##0 := _k#0 - 1;
            assert _module.Val.ValCl_q(u#1);
            assume _module.Cl.Closure_q(_module.Val.cl(u#1));
            assume _module.Cl.Closure_q(_module.Val.cl(u#1));
            // ProcessCallStmt: CheckSubrange
            c##0 := _module.Cl.env(_module.Val.cl(u#1));
            assert _module.Val.ValCl_q(v#1);
            assume _module.Cl.Closure_q(_module.Val.cl(v#1));
            assume _module.Cl.Closure_q(_module.Val.cl(v#1));
            // ProcessCallStmt: CheckSubrange
            d##0 := _module.Cl.env(_module.Val.cl(v#1));
            assert _module.Val.ValCl_q(w#1);
            assume _module.Cl.Closure_q(_module.Val.cl(w#1));
            assume _module.Cl.Closure_q(_module.Val.cl(w#1));
            // ProcessCallStmt: CheckSubrange
            e##0 := _module.Cl.env(_module.Val.cl(w#1));
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= _k#0 || _k##0 == _k#0;
            assert _k##0 < _k#0;
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem4a__ClEnvBelow__Is__Transitive_h(_k##0, c##0, d##0, e##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(201,68)"} true;
        }
        else
        {
        }
    }
    else
    {
    }
}



// function declaration for _module._default.IsCapsule
function _module.__default.IsCapsule(cap#0: DatatypeType) : bool;

function _module.__default.IsCapsule#canCall(cap#0: DatatypeType) : bool;

// consequence axiom for _module.__default.IsCapsule
axiom 48 <= $FunctionContextHeight
   ==> (forall cap#0: DatatypeType :: 
    { _module.__default.IsCapsule(cap#0) } 
    _module.__default.IsCapsule#canCall(cap#0)
         || (48 != $FunctionContextHeight && $Is(cap#0, Tclass._module.Capsule()))
       ==> true);

function _module.__default.IsCapsule#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.IsCapsule
axiom (forall cap#0: DatatypeType :: 
  { _module.__default.IsCapsule#requires(cap#0) } 
  $Is(cap#0, Tclass._module.Capsule())
     ==> _module.__default.IsCapsule#requires(cap#0) == true);

// definition axiom for _module.__default.IsCapsule (revealed)
axiom 48 <= $FunctionContextHeight
   ==> (forall cap#0: DatatypeType :: 
    { _module.__default.IsCapsule(cap#0) } 
    _module.__default.IsCapsule#canCall(cap#0)
         || (48 != $FunctionContextHeight && $Is(cap#0, Tclass._module.Capsule()))
       ==> _module.Capsule.Cap_q(cap#0)
         && _module.__default.IsCapsule(cap#0)
           == _module.Term.TermAbs_q(_module.Capsule.e(cap#0)));

// definition axiom for _module.__default.IsCapsule for all literals (revealed)
axiom 48 <= $FunctionContextHeight
   ==> (forall cap#0: DatatypeType :: 
    {:weight 3} { _module.__default.IsCapsule(Lit(cap#0)) } 
    _module.__default.IsCapsule#canCall(Lit(cap#0))
         || (48 != $FunctionContextHeight && $Is(cap#0, Tclass._module.Capsule()))
       ==> _module.Capsule.Cap_q(Lit(cap#0))
         && _module.__default.IsCapsule(Lit(cap#0))
           == Lit(_module.Term.TermAbs_q(Lit(_module.Capsule.e(Lit(cap#0))))));

procedure CheckWellformed$$_module.__default.IsCapsule(cap#0: DatatypeType where $Is(cap#0, Tclass._module.Capsule()));
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.ClosureConversion
function _module.__default.ClosureConversion(cap#0: DatatypeType) : DatatypeType;

function _module.__default.ClosureConversion#canCall(cap#0: DatatypeType) : bool;

// consequence axiom for _module.__default.ClosureConversion
axiom 49 <= $FunctionContextHeight
   ==> (forall cap#0: DatatypeType :: 
    { _module.__default.ClosureConversion(cap#0) } 
    _module.__default.ClosureConversion#canCall(cap#0)
         || (49 != $FunctionContextHeight
           && 
          $Is(cap#0, Tclass._module.Capsule())
           && _module.__default.IsCapsule(cap#0))
       ==> $Is(_module.__default.ClosureConversion(cap#0), Tclass._module.Cl()));

function _module.__default.ClosureConversion#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.ClosureConversion
axiom (forall cap#0: DatatypeType :: 
  { _module.__default.ClosureConversion#requires(cap#0) } 
  $Is(cap#0, Tclass._module.Capsule())
     ==> _module.__default.ClosureConversion#requires(cap#0)
       == _module.__default.IsCapsule(cap#0));

// definition axiom for _module.__default.ClosureConversion (revealed)
axiom 49 <= $FunctionContextHeight
   ==> (forall cap#0: DatatypeType :: 
    { _module.__default.ClosureConversion(cap#0) } 
    _module.__default.ClosureConversion#canCall(cap#0)
         || (49 != $FunctionContextHeight
           && 
          $Is(cap#0, Tclass._module.Capsule())
           && _module.__default.IsCapsule(cap#0))
       ==> _module.Capsule.Cap_q(cap#0)
         && 
        _module.Capsule.Cap_q(cap#0)
         && _module.__default.ClosureConvertedMap#canCall(_module.Capsule.s(cap#0))
         && _module.__default.ClosureConversion(cap#0)
           == #_module.Cl.Closure(_module.Term.abs(_module.Capsule.e(cap#0)), 
            _module.__default.ClosureConvertedMap($LS($LZ), _module.Capsule.s(cap#0))));

// definition axiom for _module.__default.ClosureConversion for all literals (revealed)
axiom 49 <= $FunctionContextHeight
   ==> (forall cap#0: DatatypeType :: 
    {:weight 3} { _module.__default.ClosureConversion(Lit(cap#0)) } 
    _module.__default.ClosureConversion#canCall(Lit(cap#0))
         || (49 != $FunctionContextHeight
           && 
          $Is(cap#0, Tclass._module.Capsule())
           && Lit(_module.__default.IsCapsule(Lit(cap#0))))
       ==> _module.Capsule.Cap_q(Lit(cap#0))
         && 
        _module.Capsule.Cap_q(Lit(cap#0))
         && _module.__default.ClosureConvertedMap#canCall(Lit(_module.Capsule.s(Lit(cap#0))))
         && _module.__default.ClosureConversion(Lit(cap#0))
           == Lit(#_module.Cl.Closure(Lit(_module.Term.abs(Lit(_module.Capsule.e(Lit(cap#0))))), 
              Lit(_module.__default.ClosureConvertedMap($LS($LZ), Lit(_module.Capsule.s(Lit(cap#0))))))));

procedure CheckWellformed$$_module.__default.ClosureConversion(cap#0: DatatypeType where $Is(cap#0, Tclass._module.Capsule()));
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ClosureConversion(cap#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##cap#0: DatatypeType;
  var b$reqreads#0: bool;
  var ##s#0: Map Box Box;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ClosureConversion
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(213,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##cap#0 := cap#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##cap#0, Tclass._module.Capsule(), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.IsCapsule#canCall(cap#0);
    assume _module.__default.IsCapsule(cap#0);
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.ClosureConversion(cap#0), Tclass._module.Cl());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Capsule.Cap_q(cap#0);
        assert _module.Term.TermAbs_q(_module.Capsule.e(cap#0));
        assume _module.Capsule.Cap_q(cap#0);
        ##s#0 := _module.Capsule.s(cap#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.ClosureConvertedMap#canCall(_module.Capsule.s(cap#0));
        assume _module.ClEnv.ClEnvironment_q(_module.__default.ClosureConvertedMap($LS($LZ), _module.Capsule.s(cap#0)));
        assume _module.__default.ClosureConversion(cap#0)
           == #_module.Cl.Closure(_module.Term.abs(_module.Capsule.e(cap#0)), 
            _module.__default.ClosureConvertedMap($LS($LZ), _module.Capsule.s(cap#0)));
        assume _module.Capsule.Cap_q(cap#0)
           && 
          _module.Capsule.Cap_q(cap#0)
           && _module.__default.ClosureConvertedMap#canCall(_module.Capsule.s(cap#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ClosureConversion(cap#0), Tclass._module.Cl());
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.ClosureConvertedMap
function _module.__default.ClosureConvertedMap($ly: LayerType, s#0: Map Box Box) : DatatypeType;

function _module.__default.ClosureConvertedMap#canCall(s#0: Map Box Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: Map Box Box :: 
  { _module.__default.ClosureConvertedMap($LS($ly), s#0) } 
  _module.__default.ClosureConvertedMap($LS($ly), s#0)
     == _module.__default.ClosureConvertedMap($ly, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: Map Box Box :: 
  { _module.__default.ClosureConvertedMap(AsFuelBottom($ly), s#0) } 
  _module.__default.ClosureConvertedMap($ly, s#0)
     == _module.__default.ClosureConvertedMap($LZ, s#0));

// consequence axiom for _module.__default.ClosureConvertedMap
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: Map Box Box :: 
    { _module.__default.ClosureConvertedMap($ly, s#0) } 
    _module.__default.ClosureConvertedMap#canCall(s#0)
         || (29 != $FunctionContextHeight
           && $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs())))
       ==> $Is(_module.__default.ClosureConvertedMap($ly, s#0), Tclass._module.ClEnv()));

function _module.__default.ClosureConvertedMap#requires(LayerType, Map Box Box) : bool;

// #requires axiom for _module.__default.ClosureConvertedMap
axiom (forall $ly: LayerType, s#0: Map Box Box :: 
  { _module.__default.ClosureConvertedMap#requires($ly, s#0) } 
  $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
     ==> _module.__default.ClosureConvertedMap#requires($ly, s#0) == true);

// definition axiom for _module.__default.ClosureConvertedMap (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: Map Box Box :: 
    { _module.__default.ClosureConvertedMap($LS($ly), s#0) } 
    _module.__default.ClosureConvertedMap#canCall(s#0)
         || (29 != $FunctionContextHeight
           && $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs())))
       ==> (forall y#0: Box :: 
          { $Unbox(Map#Elements(s#0)[y#0]): DatatypeType } { Map#Domain(s#0)[y#0] } 
          $IsBox(y#0, #$Var)
             ==> 
            Map#Domain(s#0)[y#0]
             ==> 
            _module.ConstOrAbs.AA_q($Unbox(Map#Elements(s#0)[y#0]): DatatypeType)
             ==> _module.__default.ClosureConvertedMap#canCall(s#0))
         && _module.__default.ClosureConvertedMap($LS($ly), s#0)
           == #_module.ClEnv.ClEnvironment(Map#Glue((lambda $w#0: Box :: $IsBox($w#0, #$Var) && Map#Domain(s#0)[$w#0]), 
              (lambda $w#0: Box :: 
                $Box((if _module.ConstOrAbs.AA_q($Unbox(Map#Elements(s#0)[$w#0]): DatatypeType)
                     then #_module.Val.ValCl(#_module.Cl.Closure(_module.ConstOrAbs.abs($Unbox(Map#Elements(s#0)[$w#0]): DatatypeType), 
                        _module.__default.ClosureConvertedMap($ly, s#0)))
                     else #_module.Val.ValConst(_module.ConstOrAbs.c($Unbox(Map#Elements(s#0)[$w#0]): DatatypeType))))), 
              TMap(#$Var, Tclass._module.Val()))));

procedure CheckWellformed$$_module.__default.ClosureConvertedMap(s#0: Map Box Box where $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs())));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ClosureConvertedMap(s#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#1: Box;
  var ##s#0: Map Box Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ClosureConvertedMap
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(220,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ClosureConvertedMap($LS($LZ), s#0), Tclass._module.ClEnv());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        havoc y#1;
        if ($IsBox(y#1, #$Var))
        {
            if (Map#Domain(s#0)[y#1])
            {
                assert Map#Domain(s#0)[y#1];
                if (_module.ConstOrAbs.AA_q($Unbox(Map#Elements(s#0)[y#1]): DatatypeType))
                {
                    assert Map#Domain(s#0)[y#1];
                    assert _module.ConstOrAbs.AA_q($Unbox(Map#Elements(s#0)[y#1]): DatatypeType);
                    ##s#0 := s#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#0, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap);
                    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.ClosureConvertedMap#canCall(s#0);
                    assume _module.ClEnv.ClEnvironment_q(_module.__default.ClosureConvertedMap($LS($LZ), s#0));
                }
                else
                {
                    assert Map#Domain(s#0)[y#1];
                    assert _module.ConstOrAbs.CC_q($Unbox(Map#Elements(s#0)[y#1]): DatatypeType);
                }
            }
        }

        // End Comprehension WF check
        assume _module.__default.ClosureConvertedMap($LS($LZ), s#0)
           == #_module.ClEnv.ClEnvironment(Map#Glue((lambda $w#2: Box :: $IsBox($w#2, #$Var) && Map#Domain(s#0)[$w#2]), 
              (lambda $w#2: Box :: 
                $Box((if _module.ConstOrAbs.AA_q($Unbox(Map#Elements(s#0)[$w#2]): DatatypeType)
                     then #_module.Val.ValCl(#_module.Cl.Closure(_module.ConstOrAbs.abs($Unbox(Map#Elements(s#0)[$w#2]): DatatypeType), 
                        _module.__default.ClosureConvertedMap($LS($LZ), s#0)))
                     else #_module.Val.ValConst(_module.ConstOrAbs.c($Unbox(Map#Elements(s#0)[$w#2]): DatatypeType))))), 
              TMap(#$Var, Tclass._module.Val())));
        assume (forall y#0: Box :: 
          { $Unbox(Map#Elements(s#0)[y#0]): DatatypeType } { Map#Domain(s#0)[y#0] } 
          $IsBox(y#0, #$Var)
             ==> 
            Map#Domain(s#0)[y#0]
             ==> 
            _module.ConstOrAbs.AA_q($Unbox(Map#Elements(s#0)[y#0]): DatatypeType)
             ==> _module.__default.ClosureConvertedMap#canCall(s#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ClosureConvertedMap($LS($LZ), s#0), Tclass._module.ClEnv());
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.CapsuleEnvironmentBelow
function _module.__default.CapsuleEnvironmentBelow(s#0: Map Box Box, t#0: Map Box Box) : bool;

function _module.__default.CapsuleEnvironmentBelow#canCall(s#0: Map Box Box, t#0: Map Box Box) : bool;

// consequence axiom for _module.__default.CapsuleEnvironmentBelow
axiom 28 <= $FunctionContextHeight
   ==> (forall s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.CapsuleEnvironmentBelow(s#0, t#0) } 
    _module.__default.CapsuleEnvironmentBelow#canCall(s#0, t#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
           && $Is(t#0, TMap(#$Var, Tclass._module.ConstOrAbs())))
       ==> true);

function _module.__default.CapsuleEnvironmentBelow#requires(Map Box Box, Map Box Box) : bool;

// #requires axiom for _module.__default.CapsuleEnvironmentBelow
axiom (forall s#0: Map Box Box, t#0: Map Box Box :: 
  { _module.__default.CapsuleEnvironmentBelow#requires(s#0, t#0) } 
  $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
       && $Is(t#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
     ==> _module.__default.CapsuleEnvironmentBelow#requires(s#0, t#0) == true);

// definition axiom for _module.__default.CapsuleEnvironmentBelow (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.CapsuleEnvironmentBelow(s#0, t#0) } 
    _module.__default.CapsuleEnvironmentBelow#canCall(s#0, t#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
           && $Is(t#0, TMap(#$Var, Tclass._module.ConstOrAbs())))
       ==> (forall y#0: Box :: 
          { $Unbox(Map#Elements(t#0)[y#0]): DatatypeType } 
            { $Unbox(Map#Elements(s#0)[y#0]): DatatypeType } 
            { Map#Domain(t#0)[y#0] } 
            { Map#Domain(s#0)[y#0] } 
          $IsBox(y#0, #$Var)
             ==> 
            (Map#Domain(s#0)[y#0]
             ==> Map#Domain(t#0)[y#0])
             ==> 
            Map#Domain(s#0)[y#0]
             ==> $IsA#_module.ConstOrAbs($Unbox(Map#Elements(s#0)[y#0]): DatatypeType)
               && $IsA#_module.ConstOrAbs($Unbox(Map#Elements(t#0)[y#0]): DatatypeType))
         && _module.__default.CapsuleEnvironmentBelow(s#0, t#0)
           == (forall y#0: Box :: 
            { $Unbox(Map#Elements(t#0)[y#0]): DatatypeType } 
              { $Unbox(Map#Elements(s#0)[y#0]): DatatypeType } 
              { Map#Domain(t#0)[y#0] } 
              { Map#Domain(s#0)[y#0] } 
            $IsBox(y#0, #$Var)
               ==> (Map#Domain(s#0)[y#0] ==> Map#Domain(t#0)[y#0])
                 && (Map#Domain(s#0)[y#0]
                   ==> _module.ConstOrAbs#Equal($Unbox(Map#Elements(s#0)[y#0]): DatatypeType, 
                    $Unbox(Map#Elements(t#0)[y#0]): DatatypeType))));

// definition axiom for _module.__default.CapsuleEnvironmentBelow for all literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall s#0: Map Box Box, t#0: Map Box Box :: 
    {:weight 3} { _module.__default.CapsuleEnvironmentBelow(Lit(s#0), Lit(t#0)) } 
    _module.__default.CapsuleEnvironmentBelow#canCall(Lit(s#0), Lit(t#0))
         || (28 != $FunctionContextHeight
           && 
          $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
           && $Is(t#0, TMap(#$Var, Tclass._module.ConstOrAbs())))
       ==> (forall y#1: Box :: 
          { $Unbox(Map#Elements(t#0)[y#1]): DatatypeType } 
            { $Unbox(Map#Elements(s#0)[y#1]): DatatypeType } 
            { Map#Domain(t#0)[y#1] } 
            { Map#Domain(s#0)[y#1] } 
          $IsBox(y#1, #$Var)
             ==> 
            (Map#Domain(s#0)[y#1]
             ==> Map#Domain(t#0)[y#1])
             ==> 
            Map#Domain(s#0)[y#1]
             ==> $IsA#_module.ConstOrAbs($Unbox(Map#Elements(Lit(s#0))[y#1]): DatatypeType)
               && $IsA#_module.ConstOrAbs($Unbox(Map#Elements(Lit(t#0))[y#1]): DatatypeType))
         && _module.__default.CapsuleEnvironmentBelow(Lit(s#0), Lit(t#0))
           == (forall y#1: Box :: 
            { $Unbox(Map#Elements(t#0)[y#1]): DatatypeType } 
              { $Unbox(Map#Elements(s#0)[y#1]): DatatypeType } 
              { Map#Domain(t#0)[y#1] } 
              { Map#Domain(s#0)[y#1] } 
            $IsBox(y#1, #$Var)
               ==> (Map#Domain(s#0)[y#1] ==> Map#Domain(t#0)[y#1])
                 && (Map#Domain(s#0)[y#1]
                   ==> _module.ConstOrAbs#Equal($Unbox(Map#Elements(Lit(s#0))[y#1]): DatatypeType, 
                    $Unbox(Map#Elements(Lit(t#0))[y#1]): DatatypeType))));

procedure CheckWellformed$$_module.__default.CapsuleEnvironmentBelow(s#0: Map Box Box where $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs())), 
    t#0: Map Box Box where $Is(t#0, TMap(#$Var, Tclass._module.ConstOrAbs())));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.CapsuleEnvironmentBelow(s#0: Map Box Box, t#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#2: Box;


    // AddWellformednessCheck for function CapsuleEnvironmentBelow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(228,10): initial state"} true;
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
        havoc y#2;
        if ($IsBox(y#2, #$Var))
        {
            if (Map#Domain(s#0)[y#2])
            {
                if (Map#Domain(t#0)[y#2])
                {
                    assert Map#Domain(s#0)[y#2];
                    assert Map#Domain(t#0)[y#2];
                }
            }
        }

        // End Comprehension WF check
        assume _module.__default.CapsuleEnvironmentBelow(s#0, t#0)
           == (forall y#3: Box :: 
            { $Unbox(Map#Elements(t#0)[y#3]): DatatypeType } 
              { $Unbox(Map#Elements(s#0)[y#3]): DatatypeType } 
              { Map#Domain(t#0)[y#3] } 
              { Map#Domain(s#0)[y#3] } 
            $IsBox(y#3, #$Var)
               ==> (Map#Domain(s#0)[y#3] ==> Map#Domain(t#0)[y#3])
                 && (Map#Domain(s#0)[y#3]
                   ==> _module.ConstOrAbs#Equal($Unbox(Map#Elements(s#0)[y#3]): DatatypeType, 
                    $Unbox(Map#Elements(t#0)[y#3]): DatatypeType)));
        assume (forall y#3: Box :: 
          { $Unbox(Map#Elements(t#0)[y#3]): DatatypeType } 
            { $Unbox(Map#Elements(s#0)[y#3]): DatatypeType } 
            { Map#Domain(t#0)[y#3] } 
            { Map#Domain(s#0)[y#3] } 
          $IsBox(y#3, #$Var)
             ==> 
            (Map#Domain(s#0)[y#3]
             ==> Map#Domain(t#0)[y#3])
             ==> 
            Map#Domain(s#0)[y#3]
             ==> $IsA#_module.ConstOrAbs($Unbox(Map#Elements(s#0)[y#3]): DatatypeType)
               && $IsA#_module.ConstOrAbs($Unbox(Map#Elements(t#0)[y#3]): DatatypeType));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.CapsuleEnvironmentBelow(s#0, t#0), TBool);
    }
}



procedure CheckWellformed$$_module.__default.Theorem5__ClosureConversion__Is__Monotone(s#0: Map Box Box
       where $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(t#0, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem5__ClosureConversion__Is__Monotone(s#0: Map Box Box
       where $Is(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(s#0, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(t#0, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap));
  // user-defined preconditions
  requires _module.__default.CapsuleEnvironmentBelow#canCall(s#0, t#0)
     ==> _module.__default.CapsuleEnvironmentBelow(s#0, t#0)
       || (forall y#0: Box :: 
        { $Unbox(Map#Elements(t#0)[y#0]): DatatypeType } 
          { $Unbox(Map#Elements(s#0)[y#0]): DatatypeType } 
          { Map#Domain(t#0)[y#0] } 
          { Map#Domain(s#0)[y#0] } 
        $IsBox(y#0, #$Var)
           ==> (Map#Domain(s#0)[y#0] ==> Map#Domain(t#0)[y#0])
             && (Map#Domain(s#0)[y#0]
               ==> _module.ConstOrAbs#Equal($Unbox(Map#Elements(s#0)[y#0]): DatatypeType, 
                $Unbox(Map#Elements(t#0)[y#0]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ClosureConvertedMap#canCall(s#0)
     && _module.__default.ClosureConvertedMap#canCall(t#0)
     && _module.__default.ClEnvBelow#canCall(_module.__default.ClosureConvertedMap($LS($LZ), s#0), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#0));
  free ensures _module.__default.ClEnvBelow#canCall(_module.__default.ClosureConvertedMap($LS($LZ), s#0), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#0))
     && 
    _module.__default.ClEnvBelow($LS($LZ), 
      _module.__default.ClosureConvertedMap($LS($LZ), s#0), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#0))
     && (forall y#1: Box :: 
      { $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#0)))[y#1]): DatatypeType } 
        { $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#0)))[y#1]): DatatypeType } 
        { Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#0)))[y#1] } 
        { Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#0)))[y#1] } 
      $IsBox(y#1, #$Var)
         ==> (Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#0)))[y#1]
             ==> Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#0)))[y#1])
           && (Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#0)))[y#1]
             ==> _module.__default.ValBelow($LS($LZ), 
              $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#0)))[y#1]): DatatypeType, 
              $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#0)))[y#1]): DatatypeType)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1} CoCall$$_module.__default.Theorem5__ClosureConversion__Is__Monotone_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: Map Box Box
       where $Is(s#1, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(s#1, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(t#1, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap));
  // user-defined preconditions
  requires _module.__default.CapsuleEnvironmentBelow#canCall(s#1, t#1)
     ==> _module.__default.CapsuleEnvironmentBelow(s#1, t#1)
       || (forall y#2: Box :: 
        { $Unbox(Map#Elements(t#1)[y#2]): DatatypeType } 
          { $Unbox(Map#Elements(s#1)[y#2]): DatatypeType } 
          { Map#Domain(t#1)[y#2] } 
          { Map#Domain(s#1)[y#2] } 
        $IsBox(y#2, #$Var)
           ==> (Map#Domain(s#1)[y#2] ==> Map#Domain(t#1)[y#2])
             && (Map#Domain(s#1)[y#2]
               ==> _module.ConstOrAbs#Equal($Unbox(Map#Elements(s#1)[y#2]): DatatypeType, 
                $Unbox(Map#Elements(t#1)[y#2]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ClosureConvertedMap#canCall(s#1)
     && _module.__default.ClosureConvertedMap#canCall(t#1)
     && _module.__default.ClEnvBelow_h#canCall(_k#0, 
      _module.__default.ClosureConvertedMap($LS($LZ), s#1), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#1));
  free ensures _module.__default.ClEnvBelow_h#canCall(_k#0, 
      _module.__default.ClosureConvertedMap($LS($LZ), s#1), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#1))
     && 
    _module.__default.ClEnvBelow_h($LS($LZ), 
      _k#0, 
      _module.__default.ClosureConvertedMap($LS($LZ), s#1), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#1))
     && (0 < _k#0
       ==> (forall y#3: Box :: 
        { $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#1)))[y#3]): DatatypeType } 
          { $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#1)))[y#3]): DatatypeType } 
          { Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#1)))[y#3] } 
          { Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#1)))[y#3] } 
        $IsBox(y#3, #$Var)
           ==> (Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#1)))[y#3]
               ==> Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#1)))[y#3])
             && (Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#1)))[y#3]
               ==> _module.__default.ValBelow_h($LS($LZ), 
                _k#0 - 1, 
                $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), s#1)))[y#3]): DatatypeType, 
                $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LZ), t#1)))[y#3]): DatatypeType))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1} Impl$$_module.__default.Theorem5__ClosureConversion__Is__Monotone_h(_k#0: int where LitInt(0) <= _k#0, 
    s#1: Map Box Box
       where $Is(s#1, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(s#1, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(#$Var, Tclass._module.ConstOrAbs()))
         && $IsAlloc(t#1, TMap(#$Var, Tclass._module.ConstOrAbs()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.CapsuleEnvironmentBelow#canCall(s#1, t#1)
     && 
    _module.__default.CapsuleEnvironmentBelow(s#1, t#1)
     && (forall y#4: Box :: 
      { $Unbox(Map#Elements(t#1)[y#4]): DatatypeType } 
        { $Unbox(Map#Elements(s#1)[y#4]): DatatypeType } 
        { Map#Domain(t#1)[y#4] } 
        { Map#Domain(s#1)[y#4] } 
      $IsBox(y#4, #$Var)
         ==> (Map#Domain(s#1)[y#4] ==> Map#Domain(t#1)[y#4])
           && (Map#Domain(s#1)[y#4]
             ==> _module.ConstOrAbs#Equal($Unbox(Map#Elements(s#1)[y#4]): DatatypeType, 
              $Unbox(Map#Elements(t#1)[y#4]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ClosureConvertedMap#canCall(s#1)
     && _module.__default.ClosureConvertedMap#canCall(t#1)
     && _module.__default.ClEnvBelow_h#canCall(_k#0, 
      _module.__default.ClosureConvertedMap($LS($LZ), s#1), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#1));
  ensures _module.__default.ClEnvBelow_h#canCall(_k#0, 
      _module.__default.ClosureConvertedMap($LS($LZ), s#1), 
      _module.__default.ClosureConvertedMap($LS($LZ), t#1))
     ==> _module.__default.ClEnvBelow_h($LS($LZ), 
        _k#0, 
        _module.__default.ClosureConvertedMap($LS($LZ), s#1), 
        _module.__default.ClosureConvertedMap($LS($LZ), t#1))
       || (0 < _k#0
         ==> (forall y#5: Box :: 
          { $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), t#1)))[y#5]): DatatypeType } 
            { $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), s#1)))[y#5]): DatatypeType } 
            { Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), t#1)))[y#5] } 
            { Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), s#1)))[y#5] } 
          $IsBox(y#5, #$Var)
             ==> (Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), s#1)))[y#5]
                 ==> Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), t#1)))[y#5])
               && (Map#Domain(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), s#1)))[y#5]
                 ==> _module.__default.ValBelow_h($LS($LS($LZ)), 
                  _k#0 - 1, 
                  $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), s#1)))[y#5]): DatatypeType, 
                  $Unbox(Map#Elements(_module.ClEnv.m(_module.__default.ClosureConvertedMap($LS($LS($LZ)), t#1)))[y#5]): DatatypeType))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, t#1} Impl$$_module.__default.Theorem5__ClosureConversion__Is__Monotone_h(_k#0: int, s#1: Map Box Box, t#1: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem5_ClosureConversion_Is_Monotone#, Impl$$_module.__default.Theorem5__ClosureConversion__Is__Monotone_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(233,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, $ih#s0#0: Map Box Box, $ih#t0#0: Map Box Box :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
           && $Is($ih#t0#0, TMap(#$Var, Tclass._module.ConstOrAbs()))
           && _module.__default.CapsuleEnvironmentBelow($ih#s0#0, $ih#t0#0)
           && ((0 <= $ih#_k0#0 && $ih#_k0#0 < _k#0)
             || ($ih#_k0#0 == _k#0
               && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#1))
                   && !Set#Subset(Map#Domain(s#1), Map#Domain($ih#s0#0)))
                 || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#1))
                   && 
                  Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#1))
                   && !Set#Subset(Map#Domain(t#1), Map#Domain($ih#t0#0))))))
         ==> _module.__default.ClEnvBelow_h($LS($LZ), 
          $ih#_k0#0, 
          _module.__default.ClosureConvertedMap($LS($LZ), $ih#s0#0), 
          _module.__default.ClosureConvertedMap($LS($LZ), $ih#t0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(236,1)
    assume true;
    if (0 < _k#0)
    {
    }
    else
    {
    }
}



// function declaration for _module._default.Bisim
function _module.__default.Bisim(_module._default.Bisim$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType)
   : bool;

function _module.__default.Bisim#canCall(_module._default.Bisim$_T0: Ty, s#0: DatatypeType, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.Bisim$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.Bisim(_module._default.Bisim$_T0, $LS($ly), s#0, t#0) } 
  _module.__default.Bisim(_module._default.Bisim$_T0, $LS($ly), s#0, t#0)
     == _module.__default.Bisim(_module._default.Bisim$_T0, $ly, s#0, t#0));

// fuel synonym axiom
axiom (forall _module._default.Bisim$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.Bisim(_module._default.Bisim$_T0, AsFuelBottom($ly), s#0, t#0) } 
  _module.__default.Bisim(_module._default.Bisim$_T0, $ly, s#0, t#0)
     == _module.__default.Bisim(_module._default.Bisim$_T0, $LZ, s#0, t#0));

// consequence axiom for _module.__default.Bisim
axiom 32 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.Bisim(_module._default.Bisim$_T0, $ly, s#0, t#0) } 
    _module.__default.Bisim#canCall(_module._default.Bisim$_T0, s#0, t#0)
         || (32 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Bisim$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.Bisim$_T0)))
       ==> true);

function _module.__default.Bisim#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Bisim
axiom (forall _module._default.Bisim$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.Bisim#requires(_module._default.Bisim$_T0, $ly, s#0, t#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.Bisim$_T0))
       && $Is(t#0, Tclass._module.Stream(_module._default.Bisim$_T0))
     ==> _module.__default.Bisim#requires(_module._default.Bisim$_T0, $ly, s#0, t#0)
       == true);

// definition axiom for _module.__default.Bisim (revealed)
axiom 32 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.Bisim(_module._default.Bisim$_T0, $LS($ly), s#0, t#0) } 
    _module.__default.Bisim#canCall(_module._default.Bisim$_T0, s#0, t#0)
         || (32 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Bisim$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.Bisim$_T0)))
       ==> _module.Stream.Cons_q(s#0)
         && _module.Stream.Cons_q(t#0)
         && (_module.Stream.hd(s#0) == _module.Stream.hd(t#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && _module.__default.Bisim#canCall(_module._default.Bisim$_T0, _module.Stream.tl(s#0), _module.Stream.tl(t#0)))
         && _module.__default.Bisim(_module._default.Bisim$_T0, $LS($ly), s#0, t#0)
           == (_module.Stream.hd(s#0) == _module.Stream.hd(t#0)
             && _module.__default.Bisim(_module._default.Bisim$_T0, $ly, _module.Stream.tl(s#0), _module.Stream.tl(t#0))));

// 1st prefix predicate axiom for _module.__default.Bisim_h
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.Bisim(_module._default.Bisim#$_T0, $LS($ly), s#0, t#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
         && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
         && _module.__default.Bisim(_module._default.Bisim#$_T0, $LS($ly), s#0, t#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0) } 
        _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0)));

// 2nd prefix predicate axiom
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.Bisim(_module._default.Bisim#$_T0, $LS($ly), s#0, t#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
         && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
         && (forall _k#0: Box :: 
          { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0) } 
          _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0))
       ==> _module.__default.Bisim(_module._default.Bisim#$_T0, $LS($ly), s#0, t#0));

// 3rd prefix predicate axiom
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      t#0: DatatypeType, 
      _k#0: Box :: 
    { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k#0, s#0, t#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
         && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k#0, s#0, t#0));

procedure CheckWellformed$$_module.__default.Bisim(_module._default.Bisim$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Bisim$_T0)), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(_module._default.Bisim$_T0)));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Bisim(_module._default.Bisim$_T0: Ty, s#0: DatatypeType, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##t#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Bisim
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(250,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(t#0);
        if (_module.Stream.hd(s#0) == _module.Stream.hd(t#0))
        {
            assume _module.Stream.Cons_q(s#0);
            assume _module.Stream.Cons_q(t#0);
            ##s#0 := _module.Stream.tl(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Bisim$_T0), $Heap);
            ##t#0 := _module.Stream.tl(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Stream(_module._default.Bisim$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Bisim#canCall(_module._default.Bisim$_T0, _module.Stream.tl(s#0), _module.Stream.tl(t#0));
        }

        assume _module.__default.Bisim(_module._default.Bisim$_T0, $LS($LZ), s#0, t#0)
           == (_module.Stream.hd(s#0) == _module.Stream.hd(t#0)
             && _module.__default.Bisim(_module._default.Bisim$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#0), 
              _module.Stream.tl(t#0)));
        assume _module.Stream.Cons_q(s#0)
           && _module.Stream.Cons_q(t#0)
           && (_module.Stream.hd(s#0) == _module.Stream.hd(t#0)
             ==> _module.Stream.Cons_q(s#0)
               && _module.Stream.Cons_q(t#0)
               && _module.__default.Bisim#canCall(_module._default.Bisim$_T0, _module.Stream.tl(s#0), _module.Stream.tl(t#0)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Bisim(_module._default.Bisim$_T0, $LS($LZ), s#0, t#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Bisim#
function _module.__default.Bisim_h(_module._default.Bisim#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    t#0: DatatypeType)
   : bool;

function _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0: Ty, _k#0: Box, s#0: DatatypeType, t#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.Bisim#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0) } 
  _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0)
     == _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k#0, s#0, t#0));

// fuel synonym axiom
axiom (forall _module._default.Bisim#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.Bisim_h(_module._default.Bisim#$_T0, AsFuelBottom($ly), _k#0, s#0, t#0) } 
  _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k#0, s#0, t#0)
     == _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LZ, _k#0, s#0, t#0));

// consequence axiom for _module.__default.Bisim_h
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k#0, s#0, t#0) } 
    _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, _k#0, s#0, t#0)
         || (33 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0)))
       ==> true);

function _module.__default.Bisim_h#requires(Ty, LayerType, Box, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Bisim_h
axiom (forall _module._default.Bisim#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.Bisim_h#requires(_module._default.Bisim#$_T0, $ly, _k#0, s#0, t#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
       && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
     ==> _module.__default.Bisim_h#requires(_module._default.Bisim#$_T0, $ly, _k#0, s#0, t#0)
       == true);

// definition axiom for _module.__default.Bisim_h (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0) } 
    _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, _k#0, s#0, t#0)
         || (33 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && (_module.Stream.hd(s#0) == _module.Stream.hd(t#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(s#0), 
                  _module.Stream.tl(t#0))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.Stream.hd(s#0) == _module.Stream.hd(t#0)
             && _module.__default.Bisim_h(_module._default.Bisim#$_T0, 
              $ly, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tl(s#0), 
              _module.Stream.tl(t#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k'#0, s#0, t#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, _k'#0, s#0, t#0)))
         && _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k#0, s#0, t#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.Stream.hd(s#0) == _module.Stream.hd(t#0)
                 && _module.__default.Bisim_h(_module._default.Bisim#$_T0, 
                  $ly, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(s#0), 
                  _module.Stream.tl(t#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k'#0, s#0, t#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.Bisim_h(_module._default.Bisim#$_T0, $ly, _k'#0, s#0, t#0)))));

// definition axiom for _module.__default.Bisim_h for decreasing-related literals (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    {:weight 3} { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), Lit(_k#0), s#0, t#0) } 
    _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, Lit(_k#0), s#0, t#0)
         || (33 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && (_module.Stream.hd(s#0) == _module.Stream.hd(t#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(s#0), 
                  _module.Stream.tl(t#0))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.Stream.hd(s#0) == _module.Stream.hd(t#0)
             && _module.__default.Bisim_h(_module._default.Bisim#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tl(s#0), 
              _module.Stream.tl(t#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k'#1, s#0, t#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, _k'#1, s#0, t#0)))
         && _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), Lit(_k#0), s#0, t#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.Stream.hd(s#0) == _module.Stream.hd(t#0)
                 && _module.__default.Bisim_h(_module._default.Bisim#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(s#0), 
                  _module.Stream.tl(t#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k'#1, s#0, t#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k'#1, s#0, t#0)))));

// definition axiom for _module.__default.Bisim_h for all literals (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.Bisim#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    {:weight 3} { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(t#0)) } 
    _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, Lit(_k#0), Lit(s#0), Lit(t#0))
         || (33 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Bisim#$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.Bisim#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(t#0)
             && (_module.Stream.hd(s#0) == _module.Stream.hd(t#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(t#0)
                 && _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(s#0), 
                  _module.Stream.tl(t#0))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.Stream.hd(s#0) == _module.Stream.hd(t#0)
             && _module.__default.Bisim_h(_module._default.Bisim#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tl(s#0), 
              _module.Stream.tl(t#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k'#2, s#0, t#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.Bisim_h#canCall(_module._default.Bisim#$_T0, _k'#2, s#0, t#0)))
         && _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(t#0))
           == ((0 < ORD#Offset(_k#0)
               ==> _module.Stream.hd(s#0) == _module.Stream.hd(t#0)
                 && _module.__default.Bisim_h(_module._default.Bisim#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(s#0), 
                  _module.Stream.tl(t#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k'#2, s#0, t#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.Bisim_h(_module._default.Bisim#$_T0, $LS($ly), _k'#2, s#0, t#0)))));

procedure CheckWellformed$$_module.__default.Theorem6__Bisim__Is__Symmetric(_module._default.Theorem6_Bisim_Is_Symmetric$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0))
         && $IsAlloc(t#0, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0), 
          $Heap)
         && $IsA#_module.Stream(t#0));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem6__Bisim__Is__Symmetric(_module._default.Theorem6_Bisim_Is_Symmetric$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0))
         && $IsAlloc(t#0, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric$_T0), 
          $Heap)
         && $IsA#_module.Stream(t#0));
  // user-defined preconditions
  requires _module.__default.Bisim#canCall(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, s#0, t#0)
     ==> _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, $LS($LZ), s#0, t#0)
       || _module.Stream.hd(s#0) == _module.Stream.hd(t#0);
  requires _module.__default.Bisim#canCall(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, s#0, t#0)
     ==> _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, $LS($LZ), s#0, t#0)
       || _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tl(s#0), 
        _module.Stream.tl(t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Bisim#canCall(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, t#0, s#0);
  free ensures _module.__default.Bisim#canCall(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, t#0, s#0)
     && 
    _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, $LS($LZ), t#0, s#0)
     && 
    _module.Stream.hd(t#0) == _module.Stream.hd(s#0)
     && _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric$_T0, 
      $LS($LZ), 
      _module.Stream.tl(t#0), 
      _module.Stream.tl(s#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1} CoCall$$_module.__default.Theorem6__Bisim__Is__Symmetric_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
         && $IsAlloc(t#1, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0), 
          $Heap)
         && $IsA#_module.Stream(t#1));
  // user-defined preconditions
  requires _module.__default.Bisim#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, s#1, t#1)
     ==> _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), s#1, t#1)
       || _module.Stream.hd(s#1) == _module.Stream.hd(t#1);
  requires _module.__default.Bisim#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, s#1, t#1)
     ==> _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), s#1, t#1)
       || _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tl(s#1), 
        _module.Stream.tl(t#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Bisim_h#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, _k#0, t#1, s#1);
  free ensures _module.__default.Bisim_h#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, _k#0, t#1, s#1)
     && 
    _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), _k#0, t#1, s#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> _module.Stream.hd(t#1) == _module.Stream.hd(s#1)
         && _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, 
          $LS($LZ), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tl(t#1), 
          _module.Stream.tl(s#1)))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), _k'#0, t#1, s#1) } 
        ORD#Less(_k'#0, _k#0)
           ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), _k'#0, t#1, s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, t#1} Impl$$_module.__default.Theorem6__Bisim__Is__Symmetric_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1), 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
         && $IsAlloc(t#1, 
          Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0), 
          $Heap)
         && $IsA#_module.Stream(t#1))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Bisim#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, s#1, t#1)
     && 
    _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), s#1, t#1)
     && 
    _module.Stream.hd(s#1) == _module.Stream.hd(t#1)
     && _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, 
      $LS($LZ), 
      _module.Stream.tl(s#1), 
      _module.Stream.tl(t#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Bisim_h#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, _k#0, t#1, s#1);
  ensures _module.__default.Bisim_h#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, _k#0, t#1, s#1)
     ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), _k#0, t#1, s#1)
       || (0 < ORD#Offset(_k#0) ==> _module.Stream.hd(t#1) == _module.Stream.hd(s#1));
  ensures _module.__default.Bisim_h#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, _k#0, t#1, s#1)
     ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), _k#0, t#1, s#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, 
          $LS($LS($LZ)), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tl(t#1), 
          _module.Stream.tl(s#1)));
  ensures _module.__default.Bisim_h#canCall(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, _k#0, t#1, s#1)
     ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), _k#0, t#1, s#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              t#1, 
              s#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              t#1, 
              s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, t#1} Impl$$_module.__default.Theorem6__Bisim__Is__Symmetric_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType, 
    t#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem6_Bisim_Is_Symmetric#, Impl$$_module.__default.Theorem6__Bisim__Is__Symmetric_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(255,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(t#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType, $ih#t0#0: DatatypeType :: 
      $Is($ih#s0#0, 
            Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
           && $Is($ih#t0#0, 
            Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
           && _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), $ih#s0#0, $ih#t0#0)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          $ih#t0#0, 
          $ih#s0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(258,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(255,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, s#2: DatatypeType, t#2: DatatypeType :: 
          $Is(s#2, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
               && $Is(t#2, Tclass._module.Stream(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0))
               && 
              ORD#Less(_k'#2, _k#0)
               && _module.__default.Bisim(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), s#2, t#2)
             ==> _module.__default.Bisim_h(_module._default.Theorem6_Bisim_Is_Symmetric#$_T0, $LS($LZ), _k'#2, t#2, s#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(255,15)"} true;
    }
}



// function declaration for _module._default.merge
function _module.__default.merge(_module._default.merge$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType)
   : DatatypeType;

function _module.__default.merge#canCall(_module._default.merge$_T0: Ty, s#0: DatatypeType, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.merge$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.merge(_module._default.merge$_T0, $LS($ly), s#0, t#0) } 
  _module.__default.merge(_module._default.merge$_T0, $LS($ly), s#0, t#0)
     == _module.__default.merge(_module._default.merge$_T0, $ly, s#0, t#0));

// fuel synonym axiom
axiom (forall _module._default.merge$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.merge(_module._default.merge$_T0, AsFuelBottom($ly), s#0, t#0) } 
  _module.__default.merge(_module._default.merge$_T0, $ly, s#0, t#0)
     == _module.__default.merge(_module._default.merge$_T0, $LZ, s#0, t#0));

// consequence axiom for _module.__default.merge
axiom 36 <= $FunctionContextHeight
   ==> (forall _module._default.merge$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.merge(_module._default.merge$_T0, $ly, s#0, t#0) } 
    _module.__default.merge#canCall(_module._default.merge$_T0, s#0, t#0)
         || (36 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.merge$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.merge$_T0)))
       ==> $Is(_module.__default.merge(_module._default.merge$_T0, $ly, s#0, t#0), 
        Tclass._module.Stream(_module._default.merge$_T0)));

function _module.__default.merge#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.merge
axiom (forall _module._default.merge$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    t#0: DatatypeType :: 
  { _module.__default.merge#requires(_module._default.merge$_T0, $ly, s#0, t#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.merge$_T0))
       && $Is(t#0, Tclass._module.Stream(_module._default.merge$_T0))
     ==> _module.__default.merge#requires(_module._default.merge$_T0, $ly, s#0, t#0)
       == true);

// definition axiom for _module.__default.merge (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall _module._default.merge$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      t#0: DatatypeType :: 
    { _module.__default.merge(_module._default.merge$_T0, $LS($ly), s#0, t#0) } 
    _module.__default.merge#canCall(_module._default.merge$_T0, s#0, t#0)
         || (36 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.merge$_T0))
           && $Is(t#0, Tclass._module.Stream(_module._default.merge$_T0)))
       ==> _module.Stream.Cons_q(s#0)
         && 
        _module.Stream.Cons_q(s#0)
         && _module.__default.merge#canCall(_module._default.merge$_T0, t#0, _module.Stream.tl(s#0))
         && _module.__default.merge(_module._default.merge$_T0, $LS($ly), s#0, t#0)
           == #_module.Stream.Cons(_module.Stream.hd(s#0), 
            _module.__default.merge(_module._default.merge$_T0, $ly, t#0, _module.Stream.tl(s#0))));

procedure CheckWellformed$$_module.__default.merge(_module._default.merge$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.merge$_T0)), 
    t#0: DatatypeType
       where $Is(t#0, Tclass._module.Stream(_module._default.merge$_T0)));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.merge(_module._default.merge$_T0: Ty, s#0: DatatypeType, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##t#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function merge
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(262,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.merge(_module._default.merge$_T0, $LS($LZ), s#0, t#0), 
          Tclass._module.Stream(_module._default.merge$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(s#0);
        ##s#0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.merge$_T0), $Heap);
        ##t#0 := _module.Stream.tl(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, Tclass._module.Stream(_module._default.merge$_T0), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.merge#canCall(_module._default.merge$_T0, t#0, _module.Stream.tl(s#0));
        assume _module.Stream.Cons_q(_module.__default.merge(_module._default.merge$_T0, $LS($LZ), t#0, _module.Stream.tl(s#0)));
        assume _module.__default.merge(_module._default.merge$_T0, $LS($LZ), s#0, t#0)
           == #_module.Stream.Cons(_module.Stream.hd(s#0), 
            _module.__default.merge(_module._default.merge$_T0, $LS($LZ), t#0, _module.Stream.tl(s#0)));
        assume _module.Stream.Cons_q(s#0)
           && 
          _module.Stream.Cons_q(s#0)
           && _module.__default.merge#canCall(_module._default.merge$_T0, t#0, _module.Stream.tl(s#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.merge(_module._default.merge$_T0, $LS($LZ), s#0, t#0), 
          Tclass._module.Stream(_module._default.merge$_T0));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.SplitLeft
function _module.__default.SplitLeft(_module._default.SplitLeft$_T0: Ty, $ly: LayerType, s#0: DatatypeType)
   : DatatypeType;

function _module.__default.SplitLeft#canCall(_module._default.SplitLeft$_T0: Ty, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.SplitLeft$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LS($ly), s#0) } 
  _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LS($ly), s#0)
     == _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $ly, s#0));

// fuel synonym axiom
axiom (forall _module._default.SplitLeft$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.SplitLeft(_module._default.SplitLeft$_T0, AsFuelBottom($ly), s#0) } 
  _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $ly, s#0)
     == _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LZ, s#0));

// consequence axiom for _module.__default.SplitLeft
axiom 37 <= $FunctionContextHeight
   ==> (forall _module._default.SplitLeft$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $ly, s#0) } 
    _module.__default.SplitLeft#canCall(_module._default.SplitLeft$_T0, s#0)
         || (37 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.SplitLeft$_T0)))
       ==> $Is(_module.__default.SplitLeft(_module._default.SplitLeft$_T0, $ly, s#0), 
        Tclass._module.Stream(_module._default.SplitLeft$_T0)));

function _module.__default.SplitLeft#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.SplitLeft
axiom (forall _module._default.SplitLeft$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.SplitLeft#requires(_module._default.SplitLeft$_T0, $ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.SplitLeft$_T0))
     ==> _module.__default.SplitLeft#requires(_module._default.SplitLeft$_T0, $ly, s#0)
       == true);

// definition axiom for _module.__default.SplitLeft (revealed)
axiom 37 <= $FunctionContextHeight
   ==> (forall _module._default.SplitLeft$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LS($ly), s#0) } 
    _module.__default.SplitLeft#canCall(_module._default.SplitLeft$_T0, s#0)
         || (37 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.SplitLeft$_T0)))
       ==> _module.Stream.Cons_q(s#0)
         && 
        _module.Stream.Cons_q(s#0)
         && _module.__default.SplitRight#canCall(_module._default.SplitLeft$_T0, _module.Stream.tl(s#0))
         && _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LS($ly), s#0)
           == #_module.Stream.Cons(_module.Stream.hd(s#0), 
            _module.__default.SplitRight(_module._default.SplitLeft$_T0, $ly, _module.Stream.tl(s#0))));

procedure CheckWellformed$$_module.__default.SplitLeft(_module._default.SplitLeft$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.SplitLeft$_T0)));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SplitLeft(_module._default.SplitLeft$_T0: Ty, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SplitLeft
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(279,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LS($LZ), s#0), 
          Tclass._module.Stream(_module._default.SplitLeft$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(s#0);
        ##s#0 := _module.Stream.tl(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.SplitLeft$_T0), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.SplitRight#canCall(_module._default.SplitLeft$_T0, _module.Stream.tl(s#0));
        assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.SplitLeft$_T0, $LS($LZ), _module.Stream.tl(s#0)));
        assume _module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LS($LZ), s#0)
           == #_module.Stream.Cons(_module.Stream.hd(s#0), 
            _module.__default.SplitRight(_module._default.SplitLeft$_T0, $LS($LZ), _module.Stream.tl(s#0)));
        assume _module.Stream.Cons_q(s#0)
           && 
          _module.Stream.Cons_q(s#0)
           && _module.__default.SplitRight#canCall(_module._default.SplitLeft$_T0, _module.Stream.tl(s#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.SplitLeft(_module._default.SplitLeft$_T0, $LS($LZ), s#0), 
          Tclass._module.Stream(_module._default.SplitLeft$_T0));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.SplitRight
function _module.__default.SplitRight(_module._default.SplitRight$_T0: Ty, $ly: LayerType, s#0: DatatypeType)
   : DatatypeType;

function _module.__default.SplitRight#canCall(_module._default.SplitRight$_T0: Ty, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.SplitRight$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.SplitRight(_module._default.SplitRight$_T0, $LS($ly), s#0) } 
  _module.__default.SplitRight(_module._default.SplitRight$_T0, $LS($ly), s#0)
     == _module.__default.SplitRight(_module._default.SplitRight$_T0, $ly, s#0));

// fuel synonym axiom
axiom (forall _module._default.SplitRight$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.SplitRight(_module._default.SplitRight$_T0, AsFuelBottom($ly), s#0) } 
  _module.__default.SplitRight(_module._default.SplitRight$_T0, $ly, s#0)
     == _module.__default.SplitRight(_module._default.SplitRight$_T0, $LZ, s#0));

// consequence axiom for _module.__default.SplitRight
axiom 37 <= $FunctionContextHeight
   ==> (forall _module._default.SplitRight$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.SplitRight(_module._default.SplitRight$_T0, $ly, s#0) } 
    _module.__default.SplitRight#canCall(_module._default.SplitRight$_T0, s#0)
         || (37 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.SplitRight$_T0)))
       ==> $Is(_module.__default.SplitRight(_module._default.SplitRight$_T0, $ly, s#0), 
        Tclass._module.Stream(_module._default.SplitRight$_T0)));

function _module.__default.SplitRight#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.SplitRight
axiom (forall _module._default.SplitRight$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.SplitRight#requires(_module._default.SplitRight$_T0, $ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.SplitRight$_T0))
     ==> _module.__default.SplitRight#requires(_module._default.SplitRight$_T0, $ly, s#0)
       == true);

// definition axiom for _module.__default.SplitRight (revealed)
axiom 37 <= $FunctionContextHeight
   ==> (forall _module._default.SplitRight$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.SplitRight(_module._default.SplitRight$_T0, $LS($ly), s#0) } 
    _module.__default.SplitRight#canCall(_module._default.SplitRight$_T0, s#0)
         || (37 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.SplitRight$_T0)))
       ==> _module.Stream.Cons_q(s#0)
         && _module.__default.SplitLeft#canCall(_module._default.SplitRight$_T0, _module.Stream.tl(s#0))
         && _module.__default.SplitRight(_module._default.SplitRight$_T0, $LS($ly), s#0)
           == _module.__default.SplitLeft(_module._default.SplitRight$_T0, $ly, _module.Stream.tl(s#0)));

procedure CheckWellformed$$_module.__default.SplitRight(_module._default.SplitRight$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.SplitRight$_T0)));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SplitRight(_module._default.SplitRight$_T0: Ty, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SplitRight
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(283,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.SplitRight(_module._default.SplitRight$_T0, $LS($LZ), s#0), 
          Tclass._module.Stream(_module._default.SplitRight$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(s#0);
        ##s#0 := _module.Stream.tl(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.SplitRight$_T0), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= LitInt(1) || LitInt(0) == LitInt(1);
        assert LitInt(0) < LitInt(1);
        assume _module.__default.SplitLeft#canCall(_module._default.SplitRight$_T0, _module.Stream.tl(s#0));
        assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.SplitRight$_T0, $LS($LZ), _module.Stream.tl(s#0)));
        assume _module.__default.SplitRight(_module._default.SplitRight$_T0, $LS($LZ), s#0)
           == _module.__default.SplitLeft(_module._default.SplitRight$_T0, $LS($LZ), _module.Stream.tl(s#0));
        assume _module.Stream.Cons_q(s#0)
           && _module.__default.SplitLeft#canCall(_module._default.SplitRight$_T0, _module.Stream.tl(s#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.SplitRight(_module._default.SplitRight$_T0, $LS($LZ), s#0), 
          Tclass._module.Stream(_module._default.SplitRight$_T0));
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Bisim(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Bisim(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, s#0)
     && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, s#0)
     && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
        $LS($LZ), 
        s#0), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
        $LS($LZ), 
        s#0))
     && _module.__default.Bisim#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          s#0), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          s#0)), 
      s#0);
  free ensures _module.__default.Bisim#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          s#0), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          s#0)), 
      s#0)
     && 
    _module.__default.Bisim(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
      $LS($LZ), 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          s#0), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          s#0)), 
      s#0)
     && 
    _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
            $LS($LZ), 
            s#0), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
            $LS($LZ), 
            s#0)))
       == _module.Stream.hd(s#0)
     && _module.__default.Bisim(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
      $LS($LZ), 
      _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
          $LS($LZ), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
            $LS($LZ), 
            s#0), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim$_T0, 
            $LS($LZ), 
            s#0))), 
      _module.Stream.tl(s#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} CoCall$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
     && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
     && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        s#1), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        s#1))
     && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _k#0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1);
  free ensures _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _k#0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1)
     && 
    _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      $LS($LZ), 
      _k#0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1)))
           == _module.Stream.hd(s#1)
         && _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1))), 
          _module.Stream.tl(s#1)))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            _k'#0, 
            _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1)), 
            s#1) } 
        ORD#Less(_k'#0, _k#0)
           ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            _k'#0, 
            _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                s#1)), 
            s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} Impl$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
     && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
     && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        s#1), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        s#1))
     && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _k#0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1);
  ensures _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _k#0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1)
     ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1)), 
        s#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LS($LZ)), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                s#1)))
           == _module.Stream.hd(s#1));
  ensures _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _k#0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1)
     ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1)), 
        s#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LS($LZ)), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LS($LZ)), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                s#1))), 
          _module.Stream.tl(s#1)));
  ensures _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
      _k#0, 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1)
     ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1)), 
        s#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  s#1)), 
              s#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  s#1)), 
              s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1} Impl$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var LHS#0: DatatypeType
     where $Is(LHS#0, 
        Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0))
       && $IsAlloc(LHS#0, 
        Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
        $Heap);
  var ##s#4: DatatypeType;
  var ##s#5: DatatypeType;
  var ##s#6: DatatypeType;
  var ##t#2: DatatypeType;
  var ##s#7: DatatypeType;
  var ##s#8: DatatypeType;
  var ##s#9: DatatypeType;
  var ##t#3: DatatypeType;
  var ##_k#0: Box;
  var ##s#10: DatatypeType;
  var ##t#4: DatatypeType;
  var _k##0: Box;
  var s##0: DatatypeType;
  var ##_k#1: Box;
  var ##s#11: DatatypeType;
  var ##t#5: DatatypeType;
  var ##s#12: DatatypeType;
  var ##s#13: DatatypeType;
  var ##s#14: DatatypeType;
  var ##t#6: DatatypeType;
  var ##s#15: DatatypeType;
  var ##s#16: DatatypeType;
  var ##s#17: DatatypeType;
  var ##t#7: DatatypeType;
  var ##s#18: DatatypeType;
  var ##s#19: DatatypeType;
  var ##s#20: DatatypeType;
  var ##t#8: DatatypeType;
  var ##s#21: DatatypeType;
  var ##s#22: DatatypeType;
  var ##s#23: DatatypeType;
  var ##t#9: DatatypeType;
  var ##s#24: DatatypeType;
  var ##s#25: DatatypeType;
  var ##s#26: DatatypeType;
  var ##t#10: DatatypeType;
  var ##s#27: DatatypeType;
  var ##s#28: DatatypeType;
  var ##s#29: DatatypeType;
  var ##t#11: DatatypeType;
  var ##_k#2: Box;
  var ##s#30: DatatypeType;
  var ##t#12: DatatypeType;
  var ##_k#3: Box;
  var ##s#31: DatatypeType;
  var ##t#13: DatatypeType;
  var ##s#32: DatatypeType;
  var ##s#33: DatatypeType;
  var ##s#34: DatatypeType;
  var ##s#35: DatatypeType;
  var ##t#14: DatatypeType;
  var ##s#36: DatatypeType;
  var ##s#37: DatatypeType;
  var ##s#38: DatatypeType;
  var ##s#39: DatatypeType;
  var ##t#15: DatatypeType;
  var ##_k#4: Box;
  var ##s#40: DatatypeType;
  var ##t#16: DatatypeType;
  var ##_k#5: Box;
  var ##s#41: DatatypeType;
  var ##t#17: DatatypeType;
  var ##_k#6: Box;
  var ##s#42: DatatypeType;
  var ##t#18: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#, Impl$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Bisim_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(288,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType :: 
      $Is($ih#s0#0, 
            Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              $ih#s0#0), 
            _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              $ih#s0#0)), 
          $ih#s0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(290,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(291,11)
        assume true;
        ##s#4 := s#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#4, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
          $Heap);
        assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
        assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1));
        ##s#5 := s#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#5, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
          $Heap);
        assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
        assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1));
        ##s#6 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#6, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
          $Heap);
        ##t#2 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          s#1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#2, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
          $Heap);
        assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1));
        assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              s#1), 
            _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              s#1)));
        assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
           && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
           && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              s#1), 
            _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              s#1));
        LHS#0 := _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
          $LS($LZ), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            s#1));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(291,47)"} true;
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assume true;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            ##_k#5 := _k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#5, TORDINAL, $Heap);
            ##s#41 := LHS#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#41, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            ##t#17 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#17, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _k#0, 
              LHS#0, 
              s#1);
            assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _k#0, 
              LHS#0, 
              s#1);
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assume _module.Stream.Cons_q(LHS#0);
            assume _module.Stream.Cons_q(s#1);
            if (_module.Stream.hd(LHS#0) == _module.Stream.hd(s#1))
            {
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume _module.Stream.Cons_q(LHS#0);
                assume _module.Stream.Cons_q(s#1);
                ##_k#6 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#6, TORDINAL, $Heap);
                ##s#42 := _module.Stream.tl(LHS#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#42, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#18 := _module.Stream.tl(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#18, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(LHS#0), 
                  _module.Stream.tl(s#1));
            }

            assume _module.Stream.Cons_q(LHS#0)
               && _module.Stream.Cons_q(s#1)
               && (_module.Stream.hd(LHS#0) == _module.Stream.hd(s#1)
                 ==> _module.Stream.Cons_q(LHS#0)
                   && _module.Stream.Cons_q(s#1)
                   && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.Stream.tl(LHS#0), 
                    _module.Stream.tl(s#1)));
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assert {:subsumption 0} _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                _k#0, 
                LHS#0, 
                s#1)
               == (_module.Stream.hd(LHS#0) == _module.Stream.hd(s#1)
                 && _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(LHS#0), 
                  _module.Stream.tl(s#1)));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assume _module.Stream.Cons_q(LHS#0);
            assume _module.Stream.Cons_q(s#1);
            if (_module.Stream.hd(LHS#0) == _module.Stream.hd(s#1))
            {
                assume ORD#IsNat(Lit(ORD#FromNat(1)));
                assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume _module.Stream.Cons_q(LHS#0);
                assume _module.Stream.Cons_q(s#1);
                ##_k#3 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#3, TORDINAL, $Heap);
                ##s#31 := _module.Stream.tl(LHS#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#31, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#13 := _module.Stream.tl(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#13, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(LHS#0), 
                  _module.Stream.tl(s#1));
            }

            assume _module.Stream.Cons_q(LHS#0)
               && _module.Stream.Cons_q(s#1)
               && (_module.Stream.hd(LHS#0) == _module.Stream.hd(s#1)
                 ==> _module.Stream.Cons_q(LHS#0)
                   && _module.Stream.Cons_q(s#1)
                   && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.Stream.tl(LHS#0), 
                    _module.Stream.tl(s#1)));
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                assume _module.Stream.Cons_q(LHS#0);
                assume _module.Stream.Cons_q(LHS#0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                assume _module.Stream.Cons_q(LHS#0);
                assume _module.Stream.Cons_q(LHS#0);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                ##s#37 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#37, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#38 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#38, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#39 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#39, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#15 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#15, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1))
                   && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1)));
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                assert {:subsumption 0} _module.Stream.hd(LHS#0)
                   == _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1)));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                ##s#33 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#33, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#34 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#34, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#35 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#35, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#14 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#14, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1))
                   && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1)));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                ##s#36 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#36, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1));
                // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                assert {:subsumption 0} _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1)))
                   == _module.Stream.hd(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      s#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                ##s#32 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#32, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                assume _module.Stream.Cons_q(s#1);
                assume _module.Stream.Cons_q(s#1);
                // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(303,6)
                assert {:subsumption 0} _module.Stream.hd(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      s#1))
                   == _module.Stream.hd(s#1);
                assume false;
            }

            assume _module.Stream.hd(LHS#0) == _module.Stream.hd(s#1);
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume _module.Stream.Cons_q(LHS#0);
            assume _module.Stream.Cons_q(s#1);
            ##_k#4 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#4, TORDINAL, $Heap);
            ##s#40 := _module.Stream.tl(LHS#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#40, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            ##t#16 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#16, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tl(LHS#0), 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(LHS#0)
               && _module.Stream.Cons_q(s#1)
               && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Stream.tl(LHS#0), 
                _module.Stream.tl(s#1));
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assert {:subsumption 0} (_module.Stream.hd(LHS#0) == _module.Stream.hd(s#1)
                 && _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tl(LHS#0), 
                  _module.Stream.tl(s#1)))
               == _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Stream.tl(LHS#0), 
                _module.Stream.tl(s#1));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assume ORD#IsNat(Lit(ORD#FromNat(1)));
            assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume _module.Stream.Cons_q(LHS#0);
            assume _module.Stream.Cons_q(s#1);
            ##_k#1 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#1, TORDINAL, $Heap);
            ##s#11 := _module.Stream.tl(LHS#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#11, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            ##t#5 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#5, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tl(LHS#0), 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(LHS#0)
               && _module.Stream.Cons_q(s#1)
               && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Stream.tl(LHS#0), 
                _module.Stream.tl(s#1));
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                assume _module.Stream.Cons_q(LHS#0);
                assume _module.Stream.Cons_q(LHS#0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                assume _module.Stream.Cons_q(LHS#0);
                assume _module.Stream.Cons_q(LHS#0);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                ##s#24 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#24, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#25 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#25, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#26 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#26, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#10 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#10, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1))
                   && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1)));
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                assert {:subsumption 0} $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  _module.Stream.tl(LHS#0), 
                  _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1))));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                ##s#18 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#18, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#19 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#19, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#20 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#20, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#8 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#8, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1))
                   && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1)));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                ##s#21 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#21, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#22 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#22, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#23 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#23, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#9 := _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#9, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1))));
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && 
                  _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1))
                   && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1)));
                // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                assert {:subsumption 0} $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1), 
                      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1))), 
                  _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LS($LZ)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      s#1), 
                    _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1))));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                ##s#12 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#12, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#13 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#13, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1);
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                ##s#14 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#14, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#6 := _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#6, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1)));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1))));
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && 
                  _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, s#1)
                   && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1))
                   && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      s#1), 
                    _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LZ), 
                        s#1)));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                assume _module.Stream.Cons_q(s#1);
                ##s#15 := _module.Stream.tl(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#15, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.Stream.tl(s#1));
                assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)));
                assume _module.Stream.Cons_q(s#1);
                ##s#16 := _module.Stream.tl(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#16, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.Stream.tl(s#1));
                assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)));
                ##s#17 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#17, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                ##t#7 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#7, 
                  Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
                  $Heap);
                assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)));
                assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tl(s#1)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tl(s#1))));
                assume _module.Stream.Cons_q(s#1)
                   && _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.Stream.tl(s#1))
                   && 
                  _module.Stream.Cons_q(s#1)
                   && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.Stream.tl(s#1))
                   && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tl(s#1)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tl(s#1)));
                // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(310,6)
                assert {:subsumption 0} $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LS($LZ)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      s#1), 
                    _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                        $LS($LS($LZ)), 
                        s#1))), 
                  _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LS($LZ)), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tl(s#1)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tl(s#1))));
                assume false;
            }

            assume $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LS($LZ)), 
              _module.Stream.tl(LHS#0), 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1))));
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume _module.Stream.Cons_q(s#1);
            ##s#27 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#27, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(s#1);
            ##s#28 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#28, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            ##s#29 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#29, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            ##t#11 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#11, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1))));
            assume _module.Stream.Cons_q(s#1);
            ##_k#2 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#2, TORDINAL, $Heap);
            ##s#30 := _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#30, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            ##t#12 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#12, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1))), 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(s#1)
               && _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                _module.Stream.tl(s#1))
               && 
              _module.Stream.Cons_q(s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                _module.Stream.tl(s#1))
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)))
               && _module.Stream.Cons_q(s#1)
               && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1))), 
                _module.Stream.tl(s#1));
            // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assert {:subsumption 0} _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Stream.tl(LHS#0), 
                _module.Stream.tl(s#1))
               == _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LS($LZ)), 
                    _module.Stream.tl(s#1)), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LS($LZ)), 
                    _module.Stream.tl(s#1))), 
                _module.Stream.tl(s#1));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assume ORD#IsNat(Lit(ORD#FromNat(1)));
            assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume _module.Stream.Cons_q(s#1);
            ##s#7 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#7, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(s#1);
            ##s#8 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#8, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            ##s#9 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#9, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            ##t#3 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#3, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1))));
            assume _module.Stream.Cons_q(s#1);
            ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#0, TORDINAL, $Heap);
            ##s#10 := _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#10, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            ##t#4 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#4, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0), 
              $Heap);
            assume _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1))), 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(s#1)
               && _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                _module.Stream.tl(s#1))
               && 
              _module.Stream.Cons_q(s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                _module.Stream.tl(s#1))
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)))
               && _module.Stream.Cons_q(s#1)
               && _module.__default.Bisim_h#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1))), 
                _module.Stream.tl(s#1));
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(317,53)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            s##0 := _module.Stream.tl(s#1);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, _k##0, s##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(317,58)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assume true;
            // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(299,3)
            assert {:subsumption 0} _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LS($LZ)), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LS($LZ)), 
                    _module.Stream.tl(s#1)), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                    $LS($LS($LZ)), 
                    _module.Stream.tl(s#1))), 
                _module.Stream.tl(s#1))
               == Lit(true);
            assume false;
        }

        assume true
           ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
            $LS($LZ), 
            _k#0, 
            LHS#0, 
            s#1);
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(288,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, s#2: DatatypeType :: 
          $Is(s#2, 
                Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0))
               && ORD#Less(_k'#2, _k#0)
             ==> _module.__default.Bisim_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
              $LS($LZ), 
              _k'#2, 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#2), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim#$_T0, 
                  $LS($LZ), 
                  s#2)), 
              s#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(288,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Equal(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Equal(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
          $LS($LZ), 
          s#0), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
          $LS($LZ), 
          s#0)))
     && $IsA#_module.Stream(s#0)
     && 
    _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, s#0)
     && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, s#0)
     && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
        $LS($LZ), 
        s#0), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
        $LS($LZ), 
        s#0));
  ensures $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
    _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
    $LS($LS($LZ)), 
    _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
      $LS($LS($LZ)), 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
        $LS($LS($LZ)), 
        s#0), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal$_T0, 
        $LS($LS($LZ)), 
        s#0)), 
    s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} CoCall$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Equal_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
     && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
     && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        s#1), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        s#1));
  free ensures $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
    _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
      $LS($LZ), 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        s#1), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        s#1)), 
    s#1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} Impl$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Equal_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1))
   returns ($_reverifyPost: bool);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
     && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
     && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
      _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        s#1), 
      _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        s#1));
  ensures $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
      _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1)
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $LS($LS($LZ)), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
            $LS($LS($LZ)), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
            $LS($LS($LZ)), 
            s#1)))
       ==> _module.Stream.Cons_q(s#1)
         && 
        _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LS($LZ)), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1)))
           == _module.Stream.hd(s#1)
         && $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LS($LZ)), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1))), 
          _module.Stream.tl(s#1)));
  ensures $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
      _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LZ), 
        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $LS($LZ), 
          s#1), 
        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $LS($LZ), 
          s#1)), 
      s#1)
     || 
    (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $LS($LS($LZ)), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
            $LS($LS($LZ)), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
            $LS($LS($LZ)), 
            s#1)))
       ==> _module.Stream.Cons_q(s#1)
         && 
        _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LS($LZ)), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1)))
           == _module.Stream.hd(s#1)
         && $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LS($LZ)), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                s#1))), 
          _module.Stream.tl(s#1)))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
        $LS($LS($LZ)), 
        _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $LS($LZ), 
          _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
            $LS($LZ), 
            s#1), 
          _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
            $LS($LZ), 
            s#1)), 
        s#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1} Impl$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Equal_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##s#3: DatatypeType;
  var ##s#4: DatatypeType;
  var ##s#5: DatatypeType;
  var ##s#6: DatatypeType;
  var ##t#1: DatatypeType;
  var ##s#7: DatatypeType;
  var ##s#8: DatatypeType;
  var ##s#9: DatatypeType;
  var ##s#10: DatatypeType;
  var ##t#2: DatatypeType;
  var ##s#11: DatatypeType;
  var ##s#12: DatatypeType;
  var ##s#13: DatatypeType;
  var ##t#3: DatatypeType;
  var _k##0: Box;
  var s##0: DatatypeType;
  var ##s#14: DatatypeType;
  var ##s#15: DatatypeType;
  var ##s#16: DatatypeType;
  var ##t#4: DatatypeType;
  var ##s#17: DatatypeType;
  var ##s#18: DatatypeType;
  var ##s#19: DatatypeType;
  var ##t#5: DatatypeType;
  var ##s#20: DatatypeType;
  var ##s#21: DatatypeType;
  var ##s#22: DatatypeType;
  var ##t#6: DatatypeType;
  var ##s#23: DatatypeType;
  var ##s#24: DatatypeType;
  var ##s#25: DatatypeType;
  var ##t#7: DatatypeType;
  var ##s#26: DatatypeType;
  var ##s#27: DatatypeType;
  var ##s#28: DatatypeType;
  var ##t#8: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#, Impl$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Equal_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(322,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType :: 
      $Is($ih#s0#0, 
            Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
            $LS($LZ), 
            _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              $ih#s0#0), 
            _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              $ih#s0#0)), 
          $ih#s0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(324,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            ##s#8 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#8, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#9 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#9, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#10 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#10, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#2 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1))
               && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1)));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            ##s#4 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#5 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#5, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#6 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#6, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#1 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1))
               && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1)));
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            ##s#7 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#7, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1));
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            assert {:subsumption 0} _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    s#1)))
               == _module.Stream.hd(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  s#1));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            ##s#3 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1));
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(328,3)
            assert {:subsumption 0} _module.Stream.hd(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  s#1))
               == _module.Stream.hd(s#1);
            assume false;
        }

        assume _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1)))
           == _module.Stream.hd(s#1);
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            ##s#26 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#26, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#27 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#27, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#28 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#28, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#8 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#8, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1))
               && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1)));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            ##s#20 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#20, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#21 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#21, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#22 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#22, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#6 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#6, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1))
               && _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1)));
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            ##s#23 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#23, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#24 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#24, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#25 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#25, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#7 := _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#7, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1))));
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && 
              _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1))
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1)));
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            assert {:subsumption 0} $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LS($LZ)), 
              _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    s#1), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    s#1))), 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  s#1), 
                _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    s#1))));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            ##s#14 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#14, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#15 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#15, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1);
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            ##s#16 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#16, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#4 := _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#4, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1))));
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && 
              _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, s#1)
               && _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1))
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#1), 
                _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    s#1)));
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            assume _module.Stream.Cons_q(s#1);
            ##s#17 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#17, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(s#1);
            ##s#18 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#18, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            ##s#19 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#19, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#5 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#5, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1))));
            assume _module.Stream.Cons_q(s#1)
               && _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.Stream.tl(s#1))
               && 
              _module.Stream.Cons_q(s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.Stream.tl(s#1))
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)));
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            assert {:subsumption 0} $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LS($LZ)), 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  s#1), 
                _module.Stream.tl(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    s#1))), 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LS($LZ)), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  _module.Stream.tl(s#1))));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            assume _module.Stream.Cons_q(s#1);
            ##s#11 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#11, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(s#1);
            ##s#12 := _module.Stream.tl(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#12, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.Stream.tl(s#1));
            assume _module.Stream.Cons_q(_module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            ##s#13 := _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#13, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            ##t#3 := _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              _module.Stream.tl(s#1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#3, 
              Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0), 
              $Heap);
            assume _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.Stream.tl(s#1)));
            assume _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1))));
            assume _module.Stream.Cons_q(s#1)
               && _module.__default.SplitLeft#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.Stream.tl(s#1))
               && 
              _module.Stream.Cons_q(s#1)
               && _module.__default.SplitRight#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.Stream.tl(s#1))
               && _module.__default.merge#canCall(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tl(s#1)));
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(341,61)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            s##0 := _module.Stream.tl(s#1);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem7__Merge__Is__Left__Inverse__Of__Split__Equal_h(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, _k##0, s##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(341,66)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ----- assert line2 ==# line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(335,3)
            assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                $LS($LS($LZ)), 
                _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1))), 
                _module.Stream.tl(s#1))
               || (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                 ==> 
                _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tl(s#1)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tl(s#1))))
                 ==> _module.Stream.Cons_q(_module.Stream.tl(s#1))
                   && 
                  _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                        $LS($LS($LZ)), 
                        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1)), 
                        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1))))
                     == _module.Stream.hd(_module.Stream.tl(s#1))
                   && $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    ORD#Minus(ORD#Minus(_k#0, ORD#FromNat(1)), ORD#FromNat(1)), 
                    $LS($LS($LZ)), 
                    _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                        $LS($LS($LZ)), 
                        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1)), 
                        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1)))), 
                    _module.Stream.tl(_module.Stream.tl(s#1))));
            assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                $LS($LS($LZ)), 
                _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1)), 
                  _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tl(s#1))), 
                _module.Stream.tl(s#1))
               || 
              (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                 ==> 
                _module.Stream.Cons_q(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LS($LZ)), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tl(s#1)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tl(s#1))))
                 ==> _module.Stream.Cons_q(_module.Stream.tl(s#1))
                   && 
                  _module.Stream.hd(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                        $LS($LS($LZ)), 
                        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1)), 
                        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1))))
                     == _module.Stream.hd(_module.Stream.tl(s#1))
                   && $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    ORD#Minus(ORD#Minus(_k#0, ORD#FromNat(1)), ORD#FromNat(1)), 
                    $LS($LS($LZ)), 
                    _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                        $LS($LS($LZ)), 
                        _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1)), 
                        _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                          $LS($LS($LZ)), 
                          _module.Stream.tl(s#1)))), 
                    _module.Stream.tl(_module.Stream.tl(s#1))))
               || (ORD#Minus(_k#0, ORD#FromNat(1)) != ORD#FromNat(0)
                   && ORD#IsLimit(ORD#Minus(_k#0, ORD#FromNat(1)))
                 ==> $Eq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                    $LS($LZ), 
                    _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tl(s#1)), 
                    _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tl(s#1))), 
                  _module.Stream.tl(s#1)));
            assume false;
        }

        assume $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tl(_module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              $LS($LZ), 
              _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1), 
              _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                s#1))), 
          _module.Stream.tl(s#1));
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(322,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, s#2: DatatypeType :: 
          $Is(s#2, 
                Tclass._module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0))
               && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.merge(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                $LS($LZ), 
                _module.__default.SplitLeft(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#2), 
                _module.__default.SplitRight(_module._default.Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal#$_T0, 
                  $LS($LZ), 
                  s#2)), 
              s#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/KozenSilva.dfy(322,15)"} true;
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

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Stream: TyTagFamily;

const unique tytagFamily$RecType: TyTagFamily;

const unique tytagFamily$Term: TyTagFamily;

const unique tytagFamily$LambdaAbs: TyTagFamily;

const unique tytagFamily$Val: TyTagFamily;

const unique tytagFamily$Cl: TyTagFamily;

const unique tytagFamily$ClEnv: TyTagFamily;

const unique tytagFamily$ConstOrAbs: TyTagFamily;

const unique tytagFamily$Capsule: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
