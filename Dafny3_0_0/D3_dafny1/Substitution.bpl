// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy -print:./Substitution.bpl

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

function Tclass._module.List() : Ty;

const unique Tagclass._module.List: TyTag;

// Tclass._module.List Tag
axiom Tag(Tclass._module.List()) == Tagclass._module.List
   && TagFamily(Tclass._module.List()) == tytagFamily$List;

// Box/unbox axiom for Tclass._module.List
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.List()) } 
  $IsBox(bx, Tclass._module.List())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.List()));

// Constructor $Is
axiom $Is(#_module.List.Nil(), Tclass._module.List());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.List.Nil(), Tclass._module.List(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.List.Nil(), Tclass._module.List(), $h));

// Constructor literal
axiom #_module.List.Nil() == Lit(#_module.List.Nil());

// Constructor function declaration
function #_module.List.Cons(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#19#0#0: DatatypeType, a#19#1#0: DatatypeType :: 
  { #_module.List.Cons(a#19#0#0, a#19#1#0) } 
  DatatypeCtorId(#_module.List.Cons(a#19#0#0, a#19#1#0)) == ##_module.List.Cons);

function _module.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d)
     ==> (exists a#20#0#0: DatatypeType, a#20#1#0: DatatypeType :: 
      d == #_module.List.Cons(a#20#0#0, a#20#1#0)));

function Tclass._module.Expr() : Ty;

const unique Tagclass._module.Expr: TyTag;

// Tclass._module.Expr Tag
axiom Tag(Tclass._module.Expr()) == Tagclass._module.Expr
   && TagFamily(Tclass._module.Expr()) == tytagFamily$Expr;

// Box/unbox axiom for Tclass._module.Expr
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Expr()) } 
  $IsBox(bx, Tclass._module.Expr())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Expr()));

// Constructor $Is
axiom (forall a#21#0#0: DatatypeType, a#21#1#0: DatatypeType :: 
  { $Is(#_module.List.Cons(a#21#0#0, a#21#1#0), Tclass._module.List()) } 
  $Is(#_module.List.Cons(a#21#0#0, a#21#1#0), Tclass._module.List())
     <==> $Is(a#21#0#0, Tclass._module.Expr()) && $Is(a#21#1#0, Tclass._module.List()));

// Constructor $IsAlloc
axiom (forall a#22#0#0: DatatypeType, a#22#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.List.Cons(a#22#0#0, a#22#1#0), Tclass._module.List(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.Cons(a#22#0#0, a#22#1#0), Tclass._module.List(), $h)
       <==> $IsAlloc(a#22#0#0, Tclass._module.Expr(), $h)
         && $IsAlloc(a#22#1#0, Tclass._module.List(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.List._h0(d), Tclass._module.Expr(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(), $h)
     ==> $IsAlloc(_module.List._h0(d), Tclass._module.Expr(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.List._h1(d), Tclass._module.List(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(), $h)
     ==> $IsAlloc(_module.List._h1(d), Tclass._module.List(), $h));

// Constructor literal
axiom (forall a#23#0#0: DatatypeType, a#23#1#0: DatatypeType :: 
  { #_module.List.Cons(Lit(a#23#0#0), Lit(a#23#1#0)) } 
  #_module.List.Cons(Lit(a#23#0#0), Lit(a#23#1#0))
     == Lit(#_module.List.Cons(a#23#0#0, a#23#1#0)));

function _module.List._h0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#24#0#0: DatatypeType, a#24#1#0: DatatypeType :: 
  { #_module.List.Cons(a#24#0#0, a#24#1#0) } 
  _module.List._h0(#_module.List.Cons(a#24#0#0, a#24#1#0)) == a#24#0#0);

// Inductive rank
axiom (forall a#25#0#0: DatatypeType, a#25#1#0: DatatypeType :: 
  { #_module.List.Cons(a#25#0#0, a#25#1#0) } 
  DtRank(a#25#0#0) < DtRank(#_module.List.Cons(a#25#0#0, a#25#1#0)));

function _module.List._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#26#0#0: DatatypeType, a#26#1#0: DatatypeType :: 
  { #_module.List.Cons(a#26#0#0, a#26#1#0) } 
  _module.List._h1(#_module.List.Cons(a#26#0#0, a#26#1#0)) == a#26#1#0);

// Inductive rank
axiom (forall a#27#0#0: DatatypeType, a#27#1#0: DatatypeType :: 
  { #_module.List.Cons(a#27#0#0, a#27#1#0) } 
  DtRank(a#27#1#0) < DtRank(#_module.List.Cons(a#27#0#0, a#27#1#0)));

// Depth-one case-split function
function $IsA#_module.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.List(d) } 
  $IsA#_module.List(d) ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d), $Is(d, Tclass._module.List()) } 
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List()) } 
  $Is(d, Tclass._module.List())
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
       <==> _module.Expr#Equal(_module.List._h0(a), _module.List._h0(b))
         && _module.List#Equal(_module.List._h1(a), _module.List._h1(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

// Constructor function declaration
function #_module.Expr.Const(int) : DatatypeType;

const unique ##_module.Expr.Const: DtCtorId;

// Constructor identifier
axiom (forall a#28#0#0: int :: 
  { #_module.Expr.Const(a#28#0#0) } 
  DatatypeCtorId(#_module.Expr.Const(a#28#0#0)) == ##_module.Expr.Const);

function _module.Expr.Const_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Expr.Const_q(d) } 
  _module.Expr.Const_q(d) <==> DatatypeCtorId(d) == ##_module.Expr.Const);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Expr.Const_q(d) } 
  _module.Expr.Const_q(d)
     ==> (exists a#29#0#0: int :: d == #_module.Expr.Const(a#29#0#0)));

// Constructor $Is
axiom (forall a#30#0#0: int :: 
  { $Is(#_module.Expr.Const(a#30#0#0), Tclass._module.Expr()) } 
  $Is(#_module.Expr.Const(a#30#0#0), Tclass._module.Expr())
     <==> $Is(a#30#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#31#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Expr.Const(a#31#0#0), Tclass._module.Expr(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Expr.Const(a#31#0#0), Tclass._module.Expr(), $h)
       <==> $IsAlloc(a#31#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expr._h2(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expr.Const_q(d)
       && $IsAlloc(d, Tclass._module.Expr(), $h)
     ==> $IsAlloc(_module.Expr._h2(d), TInt, $h));

// Constructor literal
axiom (forall a#32#0#0: int :: 
  { #_module.Expr.Const(LitInt(a#32#0#0)) } 
  #_module.Expr.Const(LitInt(a#32#0#0)) == Lit(#_module.Expr.Const(a#32#0#0)));

function _module.Expr._h2(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#33#0#0: int :: 
  { #_module.Expr.Const(a#33#0#0) } 
  _module.Expr._h2(#_module.Expr.Const(a#33#0#0)) == a#33#0#0);

// Constructor function declaration
function #_module.Expr.Var(int) : DatatypeType;

const unique ##_module.Expr.Var: DtCtorId;

// Constructor identifier
axiom (forall a#34#0#0: int :: 
  { #_module.Expr.Var(a#34#0#0) } 
  DatatypeCtorId(#_module.Expr.Var(a#34#0#0)) == ##_module.Expr.Var);

function _module.Expr.Var_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Expr.Var_q(d) } 
  _module.Expr.Var_q(d) <==> DatatypeCtorId(d) == ##_module.Expr.Var);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Expr.Var_q(d) } 
  _module.Expr.Var_q(d)
     ==> (exists a#35#0#0: int :: d == #_module.Expr.Var(a#35#0#0)));

// Constructor $Is
axiom (forall a#36#0#0: int :: 
  { $Is(#_module.Expr.Var(a#36#0#0), Tclass._module.Expr()) } 
  $Is(#_module.Expr.Var(a#36#0#0), Tclass._module.Expr()) <==> $Is(a#36#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#37#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Expr.Var(a#37#0#0), Tclass._module.Expr(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Expr.Var(a#37#0#0), Tclass._module.Expr(), $h)
       <==> $IsAlloc(a#37#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expr._h3(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expr.Var_q(d)
       && $IsAlloc(d, Tclass._module.Expr(), $h)
     ==> $IsAlloc(_module.Expr._h3(d), TInt, $h));

// Constructor literal
axiom (forall a#38#0#0: int :: 
  { #_module.Expr.Var(LitInt(a#38#0#0)) } 
  #_module.Expr.Var(LitInt(a#38#0#0)) == Lit(#_module.Expr.Var(a#38#0#0)));

function _module.Expr._h3(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#39#0#0: int :: 
  { #_module.Expr.Var(a#39#0#0) } 
  _module.Expr._h3(#_module.Expr.Var(a#39#0#0)) == a#39#0#0);

// Constructor function declaration
function #_module.Expr.Nary(int, DatatypeType) : DatatypeType;

const unique ##_module.Expr.Nary: DtCtorId;

// Constructor identifier
axiom (forall a#40#0#0: int, a#40#1#0: DatatypeType :: 
  { #_module.Expr.Nary(a#40#0#0, a#40#1#0) } 
  DatatypeCtorId(#_module.Expr.Nary(a#40#0#0, a#40#1#0)) == ##_module.Expr.Nary);

function _module.Expr.Nary_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Expr.Nary_q(d) } 
  _module.Expr.Nary_q(d) <==> DatatypeCtorId(d) == ##_module.Expr.Nary);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Expr.Nary_q(d) } 
  _module.Expr.Nary_q(d)
     ==> (exists a#41#0#0: int, a#41#1#0: DatatypeType :: 
      d == #_module.Expr.Nary(a#41#0#0, a#41#1#0)));

// Constructor $Is
axiom (forall a#42#0#0: int, a#42#1#0: DatatypeType :: 
  { $Is(#_module.Expr.Nary(a#42#0#0, a#42#1#0), Tclass._module.Expr()) } 
  $Is(#_module.Expr.Nary(a#42#0#0, a#42#1#0), Tclass._module.Expr())
     <==> $Is(a#42#0#0, TInt) && $Is(a#42#1#0, Tclass._module.List()));

// Constructor $IsAlloc
axiom (forall a#43#0#0: int, a#43#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Expr.Nary(a#43#0#0, a#43#1#0), Tclass._module.Expr(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Expr.Nary(a#43#0#0, a#43#1#0), Tclass._module.Expr(), $h)
       <==> $IsAlloc(a#43#0#0, TInt, $h) && $IsAlloc(a#43#1#0, Tclass._module.List(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expr._h4(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expr.Nary_q(d)
       && $IsAlloc(d, Tclass._module.Expr(), $h)
     ==> $IsAlloc(_module.Expr._h4(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expr._h5(d), Tclass._module.List(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expr.Nary_q(d)
       && $IsAlloc(d, Tclass._module.Expr(), $h)
     ==> $IsAlloc(_module.Expr._h5(d), Tclass._module.List(), $h));

// Constructor literal
axiom (forall a#44#0#0: int, a#44#1#0: DatatypeType :: 
  { #_module.Expr.Nary(LitInt(a#44#0#0), Lit(a#44#1#0)) } 
  #_module.Expr.Nary(LitInt(a#44#0#0), Lit(a#44#1#0))
     == Lit(#_module.Expr.Nary(a#44#0#0, a#44#1#0)));

function _module.Expr._h4(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#45#0#0: int, a#45#1#0: DatatypeType :: 
  { #_module.Expr.Nary(a#45#0#0, a#45#1#0) } 
  _module.Expr._h4(#_module.Expr.Nary(a#45#0#0, a#45#1#0)) == a#45#0#0);

function _module.Expr._h5(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#46#0#0: int, a#46#1#0: DatatypeType :: 
  { #_module.Expr.Nary(a#46#0#0, a#46#1#0) } 
  _module.Expr._h5(#_module.Expr.Nary(a#46#0#0, a#46#1#0)) == a#46#1#0);

// Inductive rank
axiom (forall a#47#0#0: int, a#47#1#0: DatatypeType :: 
  { #_module.Expr.Nary(a#47#0#0, a#47#1#0) } 
  DtRank(a#47#1#0) < DtRank(#_module.Expr.Nary(a#47#0#0, a#47#1#0)));

// Depth-one case-split function
function $IsA#_module.Expr(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Expr(d) } 
  $IsA#_module.Expr(d)
     ==> _module.Expr.Const_q(d) || _module.Expr.Var_q(d) || _module.Expr.Nary_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Expr.Nary_q(d), $Is(d, Tclass._module.Expr()) } 
    { _module.Expr.Var_q(d), $Is(d, Tclass._module.Expr()) } 
    { _module.Expr.Const_q(d), $Is(d, Tclass._module.Expr()) } 
  $Is(d, Tclass._module.Expr())
     ==> _module.Expr.Const_q(d) || _module.Expr.Var_q(d) || _module.Expr.Nary_q(d));

// Datatype extensional equality declaration
function _module.Expr#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Expr.Const
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expr#Equal(a, b), _module.Expr.Const_q(a) } 
    { _module.Expr#Equal(a, b), _module.Expr.Const_q(b) } 
  _module.Expr.Const_q(a) && _module.Expr.Const_q(b)
     ==> (_module.Expr#Equal(a, b) <==> _module.Expr._h2(a) == _module.Expr._h2(b)));

// Datatype extensional equality definition: #_module.Expr.Var
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expr#Equal(a, b), _module.Expr.Var_q(a) } 
    { _module.Expr#Equal(a, b), _module.Expr.Var_q(b) } 
  _module.Expr.Var_q(a) && _module.Expr.Var_q(b)
     ==> (_module.Expr#Equal(a, b) <==> _module.Expr._h3(a) == _module.Expr._h3(b)));

// Datatype extensional equality definition: #_module.Expr.Nary
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expr#Equal(a, b), _module.Expr.Nary_q(a) } 
    { _module.Expr#Equal(a, b), _module.Expr.Nary_q(b) } 
  _module.Expr.Nary_q(a) && _module.Expr.Nary_q(b)
     ==> (_module.Expr#Equal(a, b)
       <==> _module.Expr._h4(a) == _module.Expr._h4(b)
         && _module.List#Equal(_module.Expr._h5(a), _module.Expr._h5(b))));

// Datatype extensionality axiom: _module.Expr
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expr#Equal(a, b) } 
  _module.Expr#Equal(a, b) <==> a == b);

const unique class._module.Expr: ClassName;

// Constructor function declaration
function #_module.Expression.Const(int) : DatatypeType;

const unique ##_module.Expression.Const: DtCtorId;

// Constructor identifier
axiom (forall a#48#0#0: int :: 
  { #_module.Expression.Const(a#48#0#0) } 
  DatatypeCtorId(#_module.Expression.Const(a#48#0#0))
     == ##_module.Expression.Const);

function _module.Expression.Const_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Expression.Const_q(d) } 
  _module.Expression.Const_q(d)
     <==> DatatypeCtorId(d) == ##_module.Expression.Const);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Expression.Const_q(d) } 
  _module.Expression.Const_q(d)
     ==> (exists a#49#0#0: int :: d == #_module.Expression.Const(a#49#0#0)));

function Tclass._module.Expression() : Ty;

const unique Tagclass._module.Expression: TyTag;

// Tclass._module.Expression Tag
axiom Tag(Tclass._module.Expression()) == Tagclass._module.Expression
   && TagFamily(Tclass._module.Expression()) == tytagFamily$Expression;

// Box/unbox axiom for Tclass._module.Expression
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Expression()) } 
  $IsBox(bx, Tclass._module.Expression())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Expression()));

// Constructor $Is
axiom (forall a#50#0#0: int :: 
  { $Is(#_module.Expression.Const(a#50#0#0), Tclass._module.Expression()) } 
  $Is(#_module.Expression.Const(a#50#0#0), Tclass._module.Expression())
     <==> $Is(a#50#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#51#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Expression.Const(a#51#0#0), Tclass._module.Expression(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Expression.Const(a#51#0#0), Tclass._module.Expression(), $h)
       <==> $IsAlloc(a#51#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expression._h6(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expression.Const_q(d)
       && $IsAlloc(d, Tclass._module.Expression(), $h)
     ==> $IsAlloc(_module.Expression._h6(d), TInt, $h));

// Constructor literal
axiom (forall a#52#0#0: int :: 
  { #_module.Expression.Const(LitInt(a#52#0#0)) } 
  #_module.Expression.Const(LitInt(a#52#0#0))
     == Lit(#_module.Expression.Const(a#52#0#0)));

function _module.Expression._h6(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#53#0#0: int :: 
  { #_module.Expression.Const(a#53#0#0) } 
  _module.Expression._h6(#_module.Expression.Const(a#53#0#0)) == a#53#0#0);

// Constructor function declaration
function #_module.Expression.Var(int) : DatatypeType;

const unique ##_module.Expression.Var: DtCtorId;

// Constructor identifier
axiom (forall a#54#0#0: int :: 
  { #_module.Expression.Var(a#54#0#0) } 
  DatatypeCtorId(#_module.Expression.Var(a#54#0#0)) == ##_module.Expression.Var);

function _module.Expression.Var_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Expression.Var_q(d) } 
  _module.Expression.Var_q(d) <==> DatatypeCtorId(d) == ##_module.Expression.Var);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Expression.Var_q(d) } 
  _module.Expression.Var_q(d)
     ==> (exists a#55#0#0: int :: d == #_module.Expression.Var(a#55#0#0)));

// Constructor $Is
axiom (forall a#56#0#0: int :: 
  { $Is(#_module.Expression.Var(a#56#0#0), Tclass._module.Expression()) } 
  $Is(#_module.Expression.Var(a#56#0#0), Tclass._module.Expression())
     <==> $Is(a#56#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#57#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Expression.Var(a#57#0#0), Tclass._module.Expression(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Expression.Var(a#57#0#0), Tclass._module.Expression(), $h)
       <==> $IsAlloc(a#57#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expression._h7(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expression.Var_q(d)
       && $IsAlloc(d, Tclass._module.Expression(), $h)
     ==> $IsAlloc(_module.Expression._h7(d), TInt, $h));

// Constructor literal
axiom (forall a#58#0#0: int :: 
  { #_module.Expression.Var(LitInt(a#58#0#0)) } 
  #_module.Expression.Var(LitInt(a#58#0#0))
     == Lit(#_module.Expression.Var(a#58#0#0)));

function _module.Expression._h7(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#59#0#0: int :: 
  { #_module.Expression.Var(a#59#0#0) } 
  _module.Expression._h7(#_module.Expression.Var(a#59#0#0)) == a#59#0#0);

// Constructor function declaration
function #_module.Expression.Nary(int, Seq Box) : DatatypeType;

const unique ##_module.Expression.Nary: DtCtorId;

// Constructor identifier
axiom (forall a#60#0#0: int, a#60#1#0: Seq Box :: 
  { #_module.Expression.Nary(a#60#0#0, a#60#1#0) } 
  DatatypeCtorId(#_module.Expression.Nary(a#60#0#0, a#60#1#0))
     == ##_module.Expression.Nary);

function _module.Expression.Nary_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Expression.Nary_q(d) } 
  _module.Expression.Nary_q(d) <==> DatatypeCtorId(d) == ##_module.Expression.Nary);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Expression.Nary_q(d) } 
  _module.Expression.Nary_q(d)
     ==> (exists a#61#0#0: int, a#61#1#0: Seq Box :: 
      d == #_module.Expression.Nary(a#61#0#0, a#61#1#0)));

// Constructor $Is
axiom (forall a#62#0#0: int, a#62#1#0: Seq Box :: 
  { $Is(#_module.Expression.Nary(a#62#0#0, a#62#1#0), Tclass._module.Expression()) } 
  $Is(#_module.Expression.Nary(a#62#0#0, a#62#1#0), Tclass._module.Expression())
     <==> $Is(a#62#0#0, TInt) && $Is(a#62#1#0, TSeq(Tclass._module.Expression())));

// Constructor $IsAlloc
axiom (forall a#63#0#0: int, a#63#1#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#_module.Expression.Nary(a#63#0#0, a#63#1#0), Tclass._module.Expression(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Expression.Nary(a#63#0#0, a#63#1#0), Tclass._module.Expression(), $h)
       <==> $IsAlloc(a#63#0#0, TInt, $h)
         && $IsAlloc(a#63#1#0, TSeq(Tclass._module.Expression()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expression._h8(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expression.Nary_q(d)
       && $IsAlloc(d, Tclass._module.Expression(), $h)
     ==> $IsAlloc(_module.Expression._h8(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Expression._h9(d), TSeq(Tclass._module.Expression()), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Expression.Nary_q(d)
       && $IsAlloc(d, Tclass._module.Expression(), $h)
     ==> $IsAlloc(_module.Expression._h9(d), TSeq(Tclass._module.Expression()), $h));

// Constructor literal
axiom (forall a#64#0#0: int, a#64#1#0: Seq Box :: 
  { #_module.Expression.Nary(LitInt(a#64#0#0), Lit(a#64#1#0)) } 
  #_module.Expression.Nary(LitInt(a#64#0#0), Lit(a#64#1#0))
     == Lit(#_module.Expression.Nary(a#64#0#0, a#64#1#0)));

function _module.Expression._h8(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#65#0#0: int, a#65#1#0: Seq Box :: 
  { #_module.Expression.Nary(a#65#0#0, a#65#1#0) } 
  _module.Expression._h8(#_module.Expression.Nary(a#65#0#0, a#65#1#0)) == a#65#0#0);

function _module.Expression._h9(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#66#0#0: int, a#66#1#0: Seq Box :: 
  { #_module.Expression.Nary(a#66#0#0, a#66#1#0) } 
  _module.Expression._h9(#_module.Expression.Nary(a#66#0#0, a#66#1#0)) == a#66#1#0);

// Inductive seq element rank
axiom (forall a#67#0#0: int, a#67#1#0: Seq Box, i: int :: 
  { Seq#Index(a#67#1#0, i), #_module.Expression.Nary(a#67#0#0, a#67#1#0) } 
  0 <= i && i < Seq#Length(a#67#1#0)
     ==> DtRank($Unbox(Seq#Index(a#67#1#0, i)): DatatypeType)
       < DtRank(#_module.Expression.Nary(a#67#0#0, a#67#1#0)));

// Inductive seq rank
axiom (forall a#68#0#0: int, a#68#1#0: Seq Box :: 
  { #_module.Expression.Nary(a#68#0#0, a#68#1#0) } 
  Seq#Rank(a#68#1#0) < DtRank(#_module.Expression.Nary(a#68#0#0, a#68#1#0)));

// Depth-one case-split function
function $IsA#_module.Expression(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Expression(d) } 
  $IsA#_module.Expression(d)
     ==> _module.Expression.Const_q(d)
       || _module.Expression.Var_q(d)
       || _module.Expression.Nary_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Expression.Nary_q(d), $Is(d, Tclass._module.Expression()) } 
    { _module.Expression.Var_q(d), $Is(d, Tclass._module.Expression()) } 
    { _module.Expression.Const_q(d), $Is(d, Tclass._module.Expression()) } 
  $Is(d, Tclass._module.Expression())
     ==> _module.Expression.Const_q(d)
       || _module.Expression.Var_q(d)
       || _module.Expression.Nary_q(d));

// Datatype extensional equality declaration
function _module.Expression#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Expression.Const
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expression#Equal(a, b), _module.Expression.Const_q(a) } 
    { _module.Expression#Equal(a, b), _module.Expression.Const_q(b) } 
  _module.Expression.Const_q(a) && _module.Expression.Const_q(b)
     ==> (_module.Expression#Equal(a, b)
       <==> _module.Expression._h6(a) == _module.Expression._h6(b)));

// Datatype extensional equality definition: #_module.Expression.Var
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expression#Equal(a, b), _module.Expression.Var_q(a) } 
    { _module.Expression#Equal(a, b), _module.Expression.Var_q(b) } 
  _module.Expression.Var_q(a) && _module.Expression.Var_q(b)
     ==> (_module.Expression#Equal(a, b)
       <==> _module.Expression._h7(a) == _module.Expression._h7(b)));

// Datatype extensional equality definition: #_module.Expression.Nary
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expression#Equal(a, b), _module.Expression.Nary_q(a) } 
    { _module.Expression#Equal(a, b), _module.Expression.Nary_q(b) } 
  _module.Expression.Nary_q(a) && _module.Expression.Nary_q(b)
     ==> (_module.Expression#Equal(a, b)
       <==> _module.Expression._h8(a) == _module.Expression._h8(b)
         && Seq#Equal(_module.Expression._h9(a), _module.Expression._h9(b))));

// Datatype extensionality axiom: _module.Expression
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Expression#Equal(a, b) } 
  _module.Expression#Equal(a, b) <==> a == b);

const unique class._module.Expression: ClassName;

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

// function declaration for _module._default.Subst
function _module.__default.Subst($ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int) : DatatypeType;

function _module.__default.Subst#canCall(e#0: DatatypeType, v#0: int, val#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.Subst($LS($ly), e#0, v#0, val#0) } 
  _module.__default.Subst($LS($ly), e#0, v#0, val#0)
     == _module.__default.Subst($ly, e#0, v#0, val#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.Subst(AsFuelBottom($ly), e#0, v#0, val#0) } 
  _module.__default.Subst($ly, e#0, v#0, val#0)
     == _module.__default.Subst($LZ, e#0, v#0, val#0));

// consequence axiom for _module.__default.Subst
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
    { _module.__default.Subst($ly, e#0, v#0, val#0) } 
    _module.__default.Subst#canCall(e#0, v#0, val#0)
         || (2 != $FunctionContextHeight && $Is(e#0, Tclass._module.Expr()))
       ==> $Is(_module.__default.Subst($ly, e#0, v#0, val#0), Tclass._module.Expr()));

function _module.__default.Subst#requires(LayerType, DatatypeType, int, int) : bool;

// #requires axiom for _module.__default.Subst
axiom (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.Subst#requires($ly, e#0, v#0, val#0) } 
  $Is(e#0, Tclass._module.Expr())
     ==> _module.__default.Subst#requires($ly, e#0, v#0, val#0) == true);

// definition axiom for _module.__default.Subst (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
    { _module.__default.Subst($LS($ly), e#0, v#0, val#0) } 
    _module.__default.Subst#canCall(e#0, v#0, val#0)
         || (2 != $FunctionContextHeight && $Is(e#0, Tclass._module.Expr()))
       ==> (!_module.Expr.Const_q(e#0)
           ==> 
          !_module.Expr.Var_q(e#0)
           ==> (var args#1 := _module.Expr._h5(e#0); 
            _module.__default.SubstList#canCall(args#1, v#0, val#0)))
         && _module.__default.Subst($LS($ly), e#0, v#0, val#0)
           == (if _module.Expr.Const_q(e#0)
             then (var c#0 := _module.Expr._h2(e#0); e#0)
             else (if _module.Expr.Var_q(e#0)
               then (var x#0 := _module.Expr._h3(e#0); 
                (if x#0 == v#0 then #_module.Expr.Const(val#0) else e#0))
               else (var args#0 := _module.Expr._h5(e#0); 
                (var op#0 := _module.Expr._h4(e#0); 
                  #_module.Expr.Nary(op#0, _module.__default.SubstList($ly, args#0, v#0, val#0)))))));

// definition axiom for _module.__default.Subst for all literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
    {:weight 3} { _module.__default.Subst($LS($ly), Lit(e#0), LitInt(v#0), LitInt(val#0)) } 
    _module.__default.Subst#canCall(Lit(e#0), LitInt(v#0), LitInt(val#0))
         || (2 != $FunctionContextHeight && $Is(e#0, Tclass._module.Expr()))
       ==> (!Lit(_module.Expr.Const_q(Lit(e#0)))
           ==> 
          !Lit(_module.Expr.Var_q(Lit(e#0)))
           ==> (var args#3 := Lit(_module.Expr._h5(Lit(e#0))); 
            _module.__default.SubstList#canCall(args#3, LitInt(v#0), LitInt(val#0))))
         && _module.__default.Subst($LS($ly), Lit(e#0), LitInt(v#0), LitInt(val#0))
           == (if _module.Expr.Const_q(Lit(e#0))
             then (var c#2 := LitInt(_module.Expr._h2(Lit(e#0))); Lit(e#0))
             else (if _module.Expr.Var_q(Lit(e#0))
               then (var x#2 := LitInt(_module.Expr._h3(Lit(e#0))); 
                (if x#2 == LitInt(v#0) then #_module.Expr.Const(LitInt(val#0)) else e#0))
               else (var args#2 := Lit(_module.Expr._h5(Lit(e#0))); 
                (var op#2 := LitInt(_module.Expr._h4(Lit(e#0))); 
                  Lit(#_module.Expr.Nary(op#2, 
                      Lit(_module.__default.SubstList($LS($ly), args#2, LitInt(v#0), LitInt(val#0))))))))));

procedure CheckWellformed$$_module.__default.Subst(e#0: DatatypeType where $Is(e#0, Tclass._module.Expr()), v#0: int, val#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Subst(e#0: DatatypeType, v#0: int, val#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#2#0: int;
  var _mcc#3#0: DatatypeType;
  var args#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var op#Z#0: int;
  var let#1#0#0: int;
  var ##l#0: DatatypeType;
  var ##v#0: int;
  var ##val#0: int;
  var _mcc#1#0: int;
  var x#Z#0: int;
  var let#2#0#0: int;
  var _mcc#0#0: int;
  var c#Z#0: int;
  var let#3#0#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Subst
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(11,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Subst($LS($LZ), e#0, v#0, val#0), Tclass._module.Expr());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (e#0 == #_module.Expr.Const(_mcc#0#0))
        {
            havoc c#Z#0;
            assume true;
            assume let#3#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, TInt);
            assume c#Z#0 == let#3#0#0;
            assume _module.__default.Subst($LS($LZ), e#0, v#0, val#0) == e#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Subst($LS($LZ), e#0, v#0, val#0), Tclass._module.Expr());
        }
        else if (e#0 == #_module.Expr.Var(_mcc#1#0))
        {
            havoc x#Z#0;
            assume true;
            assume let#2#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, TInt);
            assume x#Z#0 == let#2#0#0;
            if (x#Z#0 == v#0)
            {
                assume _module.__default.Subst($LS($LZ), e#0, v#0, val#0) == #_module.Expr.Const(val#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Subst($LS($LZ), e#0, v#0, val#0), Tclass._module.Expr());
            }
            else
            {
                assume _module.__default.Subst($LS($LZ), e#0, v#0, val#0) == e#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Subst($LS($LZ), e#0, v#0, val#0), Tclass._module.Expr());
            }
        }
        else if (e#0 == #_module.Expr.Nary(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#3#0, Tclass._module.List());
            havoc args#Z#0;
            assume $Is(args#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume args#Z#0 == let#0#0#0;
            havoc op#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume op#Z#0 == let#1#0#0;
            ##l#0 := args#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.List(), $Heap);
            ##v#0 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#0, TInt, $Heap);
            ##val#0 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#0, TInt, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= v#0 || DtRank(##l#0) < DtRank(e#0) || ##v#0 == v#0;
            assert 0 <= val#0 || DtRank(##l#0) < DtRank(e#0) || ##v#0 < v#0 || ##val#0 == val#0;
            assert DtRank(##l#0) < DtRank(e#0)
               || (DtRank(##l#0) == DtRank(e#0)
                 && (##v#0 < v#0 || (##v#0 == v#0 && ##val#0 < val#0)));
            assume _module.__default.SubstList#canCall(args#Z#0, v#0, val#0);
            assume _module.__default.Subst($LS($LZ), e#0, v#0, val#0)
               == #_module.Expr.Nary(op#Z#0, _module.__default.SubstList($LS($LZ), args#Z#0, v#0, val#0));
            assume _module.__default.SubstList#canCall(args#Z#0, v#0, val#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Subst($LS($LZ), e#0, v#0, val#0), Tclass._module.Expr());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.SubstList
function _module.__default.SubstList($ly: LayerType, l#0: DatatypeType, v#0: int, val#0: int) : DatatypeType;

function _module.__default.SubstList#canCall(l#0: DatatypeType, v#0: int, val#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.SubstList($LS($ly), l#0, v#0, val#0) } 
  _module.__default.SubstList($LS($ly), l#0, v#0, val#0)
     == _module.__default.SubstList($ly, l#0, v#0, val#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.SubstList(AsFuelBottom($ly), l#0, v#0, val#0) } 
  _module.__default.SubstList($ly, l#0, v#0, val#0)
     == _module.__default.SubstList($LZ, l#0, v#0, val#0));

// consequence axiom for _module.__default.SubstList
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType, v#0: int, val#0: int :: 
    { _module.__default.SubstList($ly, l#0, v#0, val#0) } 
    _module.__default.SubstList#canCall(l#0, v#0, val#0)
         || (2 != $FunctionContextHeight && $Is(l#0, Tclass._module.List()))
       ==> $Is(_module.__default.SubstList($ly, l#0, v#0, val#0), Tclass._module.List()));

function _module.__default.SubstList#requires(LayerType, DatatypeType, int, int) : bool;

// #requires axiom for _module.__default.SubstList
axiom (forall $ly: LayerType, l#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.SubstList#requires($ly, l#0, v#0, val#0) } 
  $Is(l#0, Tclass._module.List())
     ==> _module.__default.SubstList#requires($ly, l#0, v#0, val#0) == true);

// definition axiom for _module.__default.SubstList (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType, v#0: int, val#0: int :: 
    { _module.__default.SubstList($LS($ly), l#0, v#0, val#0) } 
    _module.__default.SubstList#canCall(l#0, v#0, val#0)
         || (2 != $FunctionContextHeight && $Is(l#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(l#0)
           ==> (var tail#1 := _module.List._h1(l#0); 
            (var e#1 := _module.List._h0(l#0); 
              _module.__default.Subst#canCall(e#1, v#0, val#0)
                 && _module.__default.SubstList#canCall(tail#1, v#0, val#0))))
         && _module.__default.SubstList($LS($ly), l#0, v#0, val#0)
           == (if _module.List.Nil_q(l#0)
             then l#0
             else (var tail#0 := _module.List._h1(l#0); 
              (var e#0 := _module.List._h0(l#0); 
                #_module.List.Cons(_module.__default.Subst($ly, e#0, v#0, val#0), 
                  _module.__default.SubstList($ly, tail#0, v#0, val#0))))));

// definition axiom for _module.__default.SubstList for all literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType, v#0: int, val#0: int :: 
    {:weight 3} { _module.__default.SubstList($LS($ly), Lit(l#0), LitInt(v#0), LitInt(val#0)) } 
    _module.__default.SubstList#canCall(Lit(l#0), LitInt(v#0), LitInt(val#0))
         || (2 != $FunctionContextHeight && $Is(l#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(l#0)))
           ==> (var tail#3 := Lit(_module.List._h1(Lit(l#0))); 
            (var e#3 := Lit(_module.List._h0(Lit(l#0))); 
              _module.__default.Subst#canCall(e#3, LitInt(v#0), LitInt(val#0))
                 && _module.__default.SubstList#canCall(tail#3, LitInt(v#0), LitInt(val#0)))))
         && _module.__default.SubstList($LS($ly), Lit(l#0), LitInt(v#0), LitInt(val#0))
           == (if _module.List.Nil_q(Lit(l#0))
             then l#0
             else (var tail#2 := Lit(_module.List._h1(Lit(l#0))); 
              (var e#2 := Lit(_module.List._h0(Lit(l#0))); 
                Lit(#_module.List.Cons(Lit(_module.__default.Subst($LS($ly), e#2, LitInt(v#0), LitInt(val#0))), 
                    Lit(_module.__default.SubstList($LS($ly), tail#2, LitInt(v#0), LitInt(val#0)))))))));

procedure CheckWellformed$$_module.__default.SubstList(l#0: DatatypeType where $Is(l#0, Tclass._module.List()), v#0: int, val#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SubstList(l#0: DatatypeType, v#0: int, val#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var e#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##e#0: DatatypeType;
  var ##v#0: int;
  var ##val#0: int;
  var ##l#0: DatatypeType;
  var ##v#1: int;
  var ##val#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function SubstList
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(19,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.SubstList($LS($LZ), l#0, v#0, val#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (l#0 == #_module.List.Nil())
        {
            assume _module.__default.SubstList($LS($LZ), l#0, v#0, val#0) == l#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SubstList($LS($LZ), l#0, v#0, val#0), Tclass._module.List());
        }
        else if (l#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Expr());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume tail#Z#0 == let#0#0#0;
            havoc e#Z#0;
            assume $Is(e#Z#0, Tclass._module.Expr());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Expr());
            assume e#Z#0 == let#1#0#0;
            ##e#0 := e#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#0, Tclass._module.Expr(), $Heap);
            ##v#0 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#0, TInt, $Heap);
            ##val#0 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#0, TInt, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= v#0 || DtRank(##e#0) < DtRank(l#0) || ##v#0 == v#0;
            assert 0 <= val#0 || DtRank(##e#0) < DtRank(l#0) || ##v#0 < v#0 || ##val#0 == val#0;
            assert DtRank(##e#0) < DtRank(l#0)
               || (DtRank(##e#0) == DtRank(l#0)
                 && (##v#0 < v#0 || (##v#0 == v#0 && ##val#0 < val#0)));
            assume _module.__default.Subst#canCall(e#Z#0, v#0, val#0);
            ##l#0 := tail#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.List(), $Heap);
            ##v#1 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#1, TInt, $Heap);
            ##val#1 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#1, TInt, $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= v#0 || DtRank(##l#0) < DtRank(l#0) || ##v#1 == v#0;
            assert 0 <= val#0 || DtRank(##l#0) < DtRank(l#0) || ##v#1 < v#0 || ##val#1 == val#0;
            assert DtRank(##l#0) < DtRank(l#0)
               || (DtRank(##l#0) == DtRank(l#0)
                 && (##v#1 < v#0 || (##v#1 == v#0 && ##val#1 < val#0)));
            assume _module.__default.SubstList#canCall(tail#Z#0, v#0, val#0);
            assume _module.__default.SubstList($LS($LZ), l#0, v#0, val#0)
               == #_module.List.Cons(_module.__default.Subst($LS($LZ), e#Z#0, v#0, val#0), 
                _module.__default.SubstList($LS($LZ), tail#Z#0, v#0, val#0));
            assume _module.__default.Subst#canCall(e#Z#0, v#0, val#0)
               && _module.__default.SubstList#canCall(tail#Z#0, v#0, val#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SubstList($LS($LZ), l#0, v#0, val#0), Tclass._module.List());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure {:_induction e#0, v#0, val#0} CheckWellformed$$_module.__default.Theorem(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Expr())
         && $IsAlloc(e#0, Tclass._module.Expr(), $Heap)
         && $IsA#_module.Expr(e#0), 
    v#0: int, 
    val#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction e#0, v#0, val#0} Call$$_module.__default.Theorem(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Expr())
         && $IsAlloc(e#0, Tclass._module.Expr(), $Heap)
         && $IsA#_module.Expr(e#0), 
    v#0: int, 
    val#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Expr(_module.__default.Subst($LS($LZ), _module.__default.Subst($LS($LZ), e#0, v#0, val#0), v#0, val#0))
     && $IsA#_module.Expr(_module.__default.Subst($LS($LZ), e#0, v#0, val#0))
     && 
    _module.__default.Subst#canCall(e#0, v#0, val#0)
     && _module.__default.Subst#canCall(_module.__default.Subst($LS($LZ), e#0, v#0, val#0), v#0, val#0)
     && _module.__default.Subst#canCall(e#0, v#0, val#0);
  ensures _module.Expr#Equal(_module.__default.Subst($LS($LS($LZ)), 
      _module.__default.Subst($LS($LS($LZ)), e#0, v#0, val#0), 
      v#0, 
      val#0), 
    _module.__default.Subst($LS($LS($LZ)), e#0, v#0, val#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction e#0, v#0, val#0} Impl$$_module.__default.Theorem(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Expr())
         && $IsAlloc(e#0, Tclass._module.Expr(), $Heap)
         && $IsA#_module.Expr(e#0), 
    v#0: int, 
    val#0: int)
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Expr(_module.__default.Subst($LS($LZ), _module.__default.Subst($LS($LZ), e#0, v#0, val#0), v#0, val#0))
     && $IsA#_module.Expr(_module.__default.Subst($LS($LZ), e#0, v#0, val#0))
     && 
    _module.__default.Subst#canCall(e#0, v#0, val#0)
     && _module.__default.Subst#canCall(_module.__default.Subst($LS($LZ), e#0, v#0, val#0), v#0, val#0)
     && _module.__default.Subst#canCall(e#0, v#0, val#0);
  ensures _module.Expr#Equal(_module.__default.Subst($LS($LS($LZ)), 
      _module.__default.Subst($LS($LS($LZ)), e#0, v#0, val#0), 
      v#0, 
      val#0), 
    _module.__default.Subst($LS($LS($LZ)), e#0, v#0, val#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction e#0, v#0, val#0} Impl$$_module.__default.Theorem(e#0: DatatypeType, v#0: int, val#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#2#0_0: int;
  var _mcc#3#0_0: DatatypeType;
  var args#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var op#0_0: int;
  var let#0_1#0#0: int;
  var l##0_0: DatatypeType;
  var v##0_0: int;
  var val##0_0: int;
  var _mcc#1#1_0: int;
  var x#1_0: int;
  var let#1_0#0#0: int;
  var _mcc#0#2_0: int;
  var c#2_0: int;
  var let#2_0#0#0: int;

    // AddMethodImpl: Theorem, Impl$$_module.__default.Theorem
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(28,0): initial state"} true;
    assume $IsA#_module.Expr(e#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#e0#0: DatatypeType, $ih#v0#0: int, $ih#val0#0: int :: 
      $Is($ih#e0#0, Tclass._module.Expr())
           && Lit(true)
           && (DtRank($ih#e0#0) < DtRank(e#0)
             || (DtRank($ih#e0#0) == DtRank(e#0)
               && ((0 <= $ih#v0#0 && $ih#v0#0 < v#0)
                 || ($ih#v0#0 == v#0 && 0 <= $ih#val0#0 && $ih#val0#0 < val#0))))
         ==> _module.Expr#Equal(_module.__default.Subst($LS($LZ), 
            _module.__default.Subst($LS($LZ), $ih#e0#0, $ih#v0#0, $ih#val0#0), 
            $ih#v0#0, 
            $ih#val0#0), 
          _module.__default.Subst($LS($LZ), $ih#e0#0, $ih#v0#0, $ih#val0#0)));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#2#0_0, _mcc#3#0_0;
    havoc _mcc#1#1_0;
    havoc _mcc#0#2_0;
    if (e#0 == #_module.Expr.Const(_mcc#0#2_0))
    {
        havoc c#2_0;
        assume let#2_0#0#0 == _mcc#0#2_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_0#0#0, TInt);
        assume c#2_0 == let#2_0#0#0;
    }
    else if (e#0 == #_module.Expr.Var(_mcc#1#1_0))
    {
        havoc x#1_0;
        assume let#1_0#0#0 == _mcc#1#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_0#0#0, TInt);
        assume x#1_0 == let#1_0#0#0;
    }
    else if (e#0 == #_module.Expr.Nary(_mcc#2#0_0, _mcc#3#0_0))
    {
        assume $Is(_mcc#3#0_0, Tclass._module.List());
        havoc args#0_0;
        assume $Is(args#0_0, Tclass._module.List())
           && $IsAlloc(args#0_0, Tclass._module.List(), $Heap);
        assume let#0_0#0#0 == _mcc#3#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.List());
        assume args#0_0 == let#0_0#0#0;
        havoc op#0_0;
        assume let#0_1#0#0 == _mcc#2#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume op#0_0 == let#0_1#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(33,12)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        l##0_0 := args#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0_0 := v#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0_0 := val#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= v#0 || DtRank(l##0_0) < DtRank(e#0) || v##0_0 == v#0;
        assert 0 <= val#0 || DtRank(l##0_0) < DtRank(e#0) || v##0_0 < v#0 || val##0_0 == val#0;
        assert DtRank(l##0_0) < DtRank(e#0)
           || (DtRank(l##0_0) == DtRank(e#0)
             && (v##0_0 < v#0 || (v##0_0 == v#0 && val##0_0 < val#0)));
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Lemma(l##0_0, v##0_0, val##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(33,25)"} true;
    }
    else
    {
        assume false;
    }
}



procedure {:_induction l#0, v#0, val#0} CheckWellformed$$_module.__default.Lemma(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0), 
    v#0: int, 
    val#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction l#0, v#0, val#0} Call$$_module.__default.Lemma(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0), 
    v#0: int, 
    val#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.SubstList($LS($LZ), _module.__default.SubstList($LS($LZ), l#0, v#0, val#0), v#0, val#0))
     && $IsA#_module.List(_module.__default.SubstList($LS($LZ), l#0, v#0, val#0))
     && 
    _module.__default.SubstList#canCall(l#0, v#0, val#0)
     && _module.__default.SubstList#canCall(_module.__default.SubstList($LS($LZ), l#0, v#0, val#0), v#0, val#0)
     && _module.__default.SubstList#canCall(l#0, v#0, val#0);
  ensures _module.List#Equal(_module.__default.SubstList($LS($LS($LZ)), 
      _module.__default.SubstList($LS($LS($LZ)), l#0, v#0, val#0), 
      v#0, 
      val#0), 
    _module.__default.SubstList($LS($LS($LZ)), l#0, v#0, val#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction l#0, v#0, val#0} Impl$$_module.__default.Lemma(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0), 
    v#0: int, 
    val#0: int)
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.SubstList($LS($LZ), _module.__default.SubstList($LS($LZ), l#0, v#0, val#0), v#0, val#0))
     && $IsA#_module.List(_module.__default.SubstList($LS($LZ), l#0, v#0, val#0))
     && 
    _module.__default.SubstList#canCall(l#0, v#0, val#0)
     && _module.__default.SubstList#canCall(_module.__default.SubstList($LS($LZ), l#0, v#0, val#0), v#0, val#0)
     && _module.__default.SubstList#canCall(l#0, v#0, val#0);
  ensures _module.List#Equal(_module.__default.SubstList($LS($LS($LZ)), 
      _module.__default.SubstList($LS($LS($LZ)), l#0, v#0, val#0), 
      v#0, 
      val#0), 
    _module.__default.SubstList($LS($LS($LZ)), l#0, v#0, val#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction l#0, v#0, val#0} Impl$$_module.__default.Lemma(l#0: DatatypeType, v#0: int, val#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: DatatypeType;
  var _mcc#1#0_0: DatatypeType;
  var tail#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var e#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var e##0_0: DatatypeType;
  var v##0_0: int;
  var val##0_0: int;
  var l##0_0: DatatypeType;
  var v##0_1: int;
  var val##0_1: int;

    // AddMethodImpl: Lemma, Impl$$_module.__default.Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(39,0): initial state"} true;
    assume $IsA#_module.List(l#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#l0#0: DatatypeType, $ih#v0#0: int, $ih#val0#0: int :: 
      $Is($ih#l0#0, Tclass._module.List())
           && Lit(true)
           && (DtRank($ih#l0#0) < DtRank(l#0)
             || (DtRank($ih#l0#0) == DtRank(l#0)
               && ((0 <= $ih#v0#0 && $ih#v0#0 < v#0)
                 || ($ih#v0#0 == v#0 && 0 <= $ih#val0#0 && $ih#val0#0 < val#0))))
         ==> _module.List#Equal(_module.__default.SubstList($LS($LZ), 
            _module.__default.SubstList($LS($LZ), $ih#l0#0, $ih#v0#0, $ih#val0#0), 
            $ih#v0#0, 
            $ih#val0#0), 
          _module.__default.SubstList($LS($LZ), $ih#l0#0, $ih#v0#0, $ih#val0#0)));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (l#0 == #_module.List.Nil())
    {
    }
    else if (l#0 == #_module.List.Cons(_mcc#0#0_0, _mcc#1#0_0))
    {
        assume $Is(_mcc#0#0_0, Tclass._module.Expr());
        assume $Is(_mcc#1#0_0, Tclass._module.List());
        havoc tail#0_0;
        assume $Is(tail#0_0, Tclass._module.List())
           && $IsAlloc(tail#0_0, Tclass._module.List(), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.List());
        assume tail#0_0 == let#0_0#0#0;
        havoc e#0_0;
        assume $Is(e#0_0, Tclass._module.Expr())
           && $IsAlloc(e#0_0, Tclass._module.Expr(), $Heap);
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.Expr());
        assume e#0_0 == let#0_1#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(43,14)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0_0 := e#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0_0 := v#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0_0 := val#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= v#0 || DtRank(e##0_0) < DtRank(l#0) || v##0_0 == v#0;
        assert 0 <= val#0 || DtRank(e##0_0) < DtRank(l#0) || v##0_0 < v#0 || val##0_0 == val#0;
        assert DtRank(e##0_0) < DtRank(l#0)
           || (DtRank(e##0_0) == DtRank(l#0)
             && (v##0_0 < v#0 || (v##0_0 == v#0 && val##0_0 < val#0)));
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Theorem(e##0_0, v##0_0, val##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(43,24)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(44,12)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        l##0_0 := tail#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0_1 := v#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0_1 := val#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= v#0 || DtRank(l##0_0) < DtRank(l#0) || v##0_1 == v#0;
        assert 0 <= val#0 || DtRank(l##0_0) < DtRank(l#0) || v##0_1 < v#0 || val##0_1 == val#0;
        assert DtRank(l##0_0) < DtRank(l#0)
           || (DtRank(l##0_0) == DtRank(l#0)
             && (v##0_1 < v#0 || (v##0_1 == v#0 && val##0_1 < val#0)));
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Lemma(l##0_0, v##0_1, val##0_1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(44,25)"} true;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.Substitute
function _module.__default.Substitute($ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int) : DatatypeType;

function _module.__default.Substitute#canCall(e#0: DatatypeType, v#0: int, val#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.Substitute($LS($ly), e#0, v#0, val#0) } 
  _module.__default.Substitute($LS($ly), e#0, v#0, val#0)
     == _module.__default.Substitute($ly, e#0, v#0, val#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.Substitute(AsFuelBottom($ly), e#0, v#0, val#0) } 
  _module.__default.Substitute($ly, e#0, v#0, val#0)
     == _module.__default.Substitute($LZ, e#0, v#0, val#0));

// consequence axiom for _module.__default.Substitute
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
    { _module.__default.Substitute($ly, e#0, v#0, val#0) } 
    _module.__default.Substitute#canCall(e#0, v#0, val#0)
         || (4 != $FunctionContextHeight && $Is(e#0, Tclass._module.Expression()))
       ==> $Is(_module.__default.Substitute($ly, e#0, v#0, val#0), Tclass._module.Expression()));

function _module.__default.Substitute#requires(LayerType, DatatypeType, int, int) : bool;

// #requires axiom for _module.__default.Substitute
axiom (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
  { _module.__default.Substitute#requires($ly, e#0, v#0, val#0) } 
  $Is(e#0, Tclass._module.Expression())
     ==> _module.__default.Substitute#requires($ly, e#0, v#0, val#0) == true);

// definition axiom for _module.__default.Substitute (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
    { _module.__default.Substitute($LS($ly), e#0, v#0, val#0) } 
    _module.__default.Substitute#canCall(e#0, v#0, val#0)
         || (4 != $FunctionContextHeight && $Is(e#0, Tclass._module.Expression()))
       ==> (!_module.Expression.Const_q(e#0)
           ==> 
          !_module.Expression.Var_q(e#0)
           ==> (var args#1 := _module.Expression._h9(e#0); 
            _module.__default.SubstSeq#canCall(e#0, args#1, v#0, val#0)))
         && _module.__default.Substitute($LS($ly), e#0, v#0, val#0)
           == (if _module.Expression.Const_q(e#0)
             then (var c#0 := _module.Expression._h6(e#0); e#0)
             else (if _module.Expression.Var_q(e#0)
               then (var x#0 := _module.Expression._h7(e#0); 
                (if x#0 == v#0 then #_module.Expression.Const(val#0) else e#0))
               else (var args#0 := _module.Expression._h9(e#0); 
                (var op#0 := _module.Expression._h8(e#0); 
                  #_module.Expression.Nary(op#0, _module.__default.SubstSeq($ly, e#0, args#0, v#0, val#0)))))));

// definition axiom for _module.__default.Substitute for decreasing-related literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
    {:weight 3} { _module.__default.Substitute($LS($ly), Lit(e#0), v#0, val#0) } 
    _module.__default.Substitute#canCall(Lit(e#0), v#0, val#0)
         || (4 != $FunctionContextHeight && $Is(e#0, Tclass._module.Expression()))
       ==> (!Lit(_module.Expression.Const_q(Lit(e#0)))
           ==> 
          !Lit(_module.Expression.Var_q(Lit(e#0)))
           ==> (var args#3 := Lit(_module.Expression._h9(Lit(e#0))); 
            _module.__default.SubstSeq#canCall(Lit(e#0), args#3, v#0, val#0)))
         && _module.__default.Substitute($LS($ly), Lit(e#0), v#0, val#0)
           == (if _module.Expression.Const_q(Lit(e#0))
             then (var c#2 := LitInt(_module.Expression._h6(Lit(e#0))); Lit(e#0))
             else (if _module.Expression.Var_q(Lit(e#0))
               then (var x#2 := LitInt(_module.Expression._h7(Lit(e#0))); 
                (if x#2 == v#0 then #_module.Expression.Const(val#0) else e#0))
               else (var args#2 := Lit(_module.Expression._h9(Lit(e#0))); 
                (var op#2 := LitInt(_module.Expression._h8(Lit(e#0))); 
                  #_module.Expression.Nary(op#2, _module.__default.SubstSeq($LS($ly), Lit(e#0), args#2, v#0, val#0)))))));

// definition axiom for _module.__default.Substitute for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType, v#0: int, val#0: int :: 
    {:weight 3} { _module.__default.Substitute($LS($ly), Lit(e#0), LitInt(v#0), LitInt(val#0)) } 
    _module.__default.Substitute#canCall(Lit(e#0), LitInt(v#0), LitInt(val#0))
         || (4 != $FunctionContextHeight && $Is(e#0, Tclass._module.Expression()))
       ==> (!Lit(_module.Expression.Const_q(Lit(e#0)))
           ==> 
          !Lit(_module.Expression.Var_q(Lit(e#0)))
           ==> (var args#5 := Lit(_module.Expression._h9(Lit(e#0))); 
            _module.__default.SubstSeq#canCall(Lit(e#0), args#5, LitInt(v#0), LitInt(val#0))))
         && _module.__default.Substitute($LS($ly), Lit(e#0), LitInt(v#0), LitInt(val#0))
           == (if _module.Expression.Const_q(Lit(e#0))
             then (var c#4 := LitInt(_module.Expression._h6(Lit(e#0))); Lit(e#0))
             else (if _module.Expression.Var_q(Lit(e#0))
               then (var x#4 := LitInt(_module.Expression._h7(Lit(e#0))); 
                (if x#4 == LitInt(v#0) then #_module.Expression.Const(LitInt(val#0)) else e#0))
               else (var args#4 := Lit(_module.Expression._h9(Lit(e#0))); 
                (var op#4 := LitInt(_module.Expression._h8(Lit(e#0))); 
                  Lit(#_module.Expression.Nary(op#4, 
                      Lit(_module.__default.SubstSeq($LS($ly), Lit(e#0), args#4, LitInt(v#0), LitInt(val#0))))))))));

procedure CheckWellformed$$_module.__default.Substitute(e#0: DatatypeType where $Is(e#0, Tclass._module.Expression()), 
    v#0: int, 
    val#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Substitute(e#0: DatatypeType, v#0: int, val#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#2#0: int;
  var _mcc#3#0: Seq Box;
  var args#Z#0: Seq Box;
  var let#0#0#0: Seq Box;
  var op#Z#0: int;
  var let#1#0#0: int;
  var ##parent#0: DatatypeType;
  var ##q#0: Seq Box;
  var ##v#0: int;
  var ##val#0: int;
  var _mcc#1#0: int;
  var x#Z#0: int;
  var let#2#0#0: int;
  var _mcc#0#0: int;
  var c#Z#0: int;
  var let#3#0#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Substitute
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(55,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0), 
          Tclass._module.Expression());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (e#0 == #_module.Expression.Const(_mcc#0#0))
        {
            havoc c#Z#0;
            assume true;
            assume let#3#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, TInt);
            assume c#Z#0 == let#3#0#0;
            assume _module.__default.Substitute($LS($LZ), e#0, v#0, val#0) == e#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0), 
              Tclass._module.Expression());
        }
        else if (e#0 == #_module.Expression.Var(_mcc#1#0))
        {
            havoc x#Z#0;
            assume true;
            assume let#2#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, TInt);
            assume x#Z#0 == let#2#0#0;
            if (x#Z#0 == v#0)
            {
                assume _module.__default.Substitute($LS($LZ), e#0, v#0, val#0)
                   == #_module.Expression.Const(val#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0), 
                  Tclass._module.Expression());
            }
            else
            {
                assume _module.__default.Substitute($LS($LZ), e#0, v#0, val#0) == e#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0), 
                  Tclass._module.Expression());
            }
        }
        else if (e#0 == #_module.Expression.Nary(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#3#0, TSeq(Tclass._module.Expression()));
            havoc args#Z#0;
            assume $Is(args#Z#0, TSeq(Tclass._module.Expression()));
            assume let#0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, TSeq(Tclass._module.Expression()));
            assume args#Z#0 == let#0#0#0;
            havoc op#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume op#Z#0 == let#1#0#0;
            ##parent#0 := e#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##parent#0, Tclass._module.Expression(), $Heap);
            ##q#0 := args#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##q#0, TSeq(Tclass._module.Expression()), $Heap);
            ##v#0 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#0, TInt, $Heap);
            ##val#0 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#0, TInt, $Heap);
            assert {:subsumption 0} (forall a#0: DatatypeType :: 
              { Seq#Contains(##q#0, $Box(a#0)) } 
              $Is(a#0, Tclass._module.Expression())
                 ==> 
                Seq#Contains(##q#0, $Box(a#0))
                 ==> DtRank(a#0) < DtRank(##parent#0));
            assume (forall a#0: DatatypeType :: 
              { Seq#Contains(##q#0, $Box(a#0)) } 
              $Is(a#0, Tclass._module.Expression())
                 ==> 
                Seq#Contains(##q#0, $Box(a#0))
                 ==> DtRank(a#0) < DtRank(##parent#0));
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##parent#0) <= DtRank(e#0)
               && (DtRank(##parent#0) == DtRank(e#0) ==> true);
            assume _module.__default.SubstSeq#canCall(e#0, args#Z#0, v#0, val#0);
            assume _module.__default.Substitute($LS($LZ), e#0, v#0, val#0)
               == #_module.Expression.Nary(op#Z#0, _module.__default.SubstSeq($LS($LZ), e#0, args#Z#0, v#0, val#0));
            assume _module.__default.SubstSeq#canCall(e#0, args#Z#0, v#0, val#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0), 
              Tclass._module.Expression());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.SubstSeq
function _module.__default.SubstSeq($ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int)
   : Seq Box;

function _module.__default.SubstSeq#canCall(parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int :: 
  { _module.__default.SubstSeq($LS($ly), parent#0, q#0, v#0, val#0) } 
  _module.__default.SubstSeq($LS($ly), parent#0, q#0, v#0, val#0)
     == _module.__default.SubstSeq($ly, parent#0, q#0, v#0, val#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int :: 
  { _module.__default.SubstSeq(AsFuelBottom($ly), parent#0, q#0, v#0, val#0) } 
  _module.__default.SubstSeq($ly, parent#0, q#0, v#0, val#0)
     == _module.__default.SubstSeq($LZ, parent#0, q#0, v#0, val#0));

// consequence axiom for _module.__default.SubstSeq
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int :: 
    { _module.__default.SubstSeq($ly, parent#0, q#0, v#0, val#0) } 
    _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(parent#0, Tclass._module.Expression())
           && $Is(q#0, TSeq(Tclass._module.Expression()))
           && (forall a#0: DatatypeType :: 
            { Seq#Contains(q#0, $Box(a#0)) } 
            $Is(a#0, Tclass._module.Expression())
               ==> 
              Seq#Contains(q#0, $Box(a#0))
               ==> DtRank(a#0) < DtRank(parent#0)))
       ==> $Is(_module.__default.SubstSeq($ly, parent#0, q#0, v#0, val#0), 
        TSeq(Tclass._module.Expression())));

function _module.__default.SubstSeq#requires(LayerType, DatatypeType, Seq Box, int, int) : bool;

// #requires axiom for _module.__default.SubstSeq
axiom (forall $ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int :: 
  { _module.__default.SubstSeq#requires($ly, parent#0, q#0, v#0, val#0) } 
  $Is(parent#0, Tclass._module.Expression())
       && $Is(q#0, TSeq(Tclass._module.Expression()))
     ==> _module.__default.SubstSeq#requires($ly, parent#0, q#0, v#0, val#0)
       == (forall a#1: DatatypeType :: 
        { Seq#Contains(q#0, $Box(a#1)) } 
        $Is(a#1, Tclass._module.Expression())
           ==> 
          Seq#Contains(q#0, $Box(a#1))
           ==> DtRank(a#1) < DtRank(parent#0)));

// definition axiom for _module.__default.SubstSeq (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int :: 
    { _module.__default.SubstSeq($LS($ly), parent#0, q#0, v#0, val#0) } 
    _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(parent#0, Tclass._module.Expression())
           && $Is(q#0, TSeq(Tclass._module.Expression()))
           && (forall a#1: DatatypeType :: 
            { Seq#Contains(q#0, $Box(a#1)) } 
            $Is(a#1, Tclass._module.Expression())
               ==> 
              Seq#Contains(q#0, $Box(a#1))
               ==> DtRank(a#1) < DtRank(parent#0)))
       ==> (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
           ==> _module.__default.SubstSeq#canCall(parent#0, Seq#Take(q#0, Seq#Length(q#0) - 1), v#0, val#0)
             && _module.__default.Substitute#canCall($Unbox(Seq#Index(q#0, Seq#Length(q#0) - 1)): DatatypeType, v#0, val#0))
         && _module.__default.SubstSeq($LS($ly), parent#0, q#0, v#0, val#0)
           == (if Seq#Equal(q#0, Seq#Empty(): Seq Box)
             then Seq#Empty(): Seq Box
             else Seq#Append(_module.__default.SubstSeq($ly, parent#0, Seq#Take(q#0, Seq#Length(q#0) - 1), v#0, val#0), 
              Seq#Build(Seq#Empty(): Seq Box, 
                $Box(_module.__default.Substitute($ly, $Unbox(Seq#Index(q#0, Seq#Length(q#0) - 1)): DatatypeType, v#0, val#0))))));

// definition axiom for _module.__default.SubstSeq for decreasing-related literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int :: 
    {:weight 3} { _module.__default.SubstSeq($LS($ly), Lit(parent#0), Lit(q#0), v#0, val#0) } 
    _module.__default.SubstSeq#canCall(Lit(parent#0), Lit(q#0), v#0, val#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(parent#0, Tclass._module.Expression())
           && $Is(q#0, TSeq(Tclass._module.Expression()))
           && (forall a#2: DatatypeType :: 
            { Seq#Contains(q#0, $Box(a#2)) } 
            $Is(a#2, Tclass._module.Expression())
               ==> 
              Seq#Contains(q#0, $Box(a#2))
               ==> DtRank(a#2) < DtRank(parent#0)))
       ==> (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
           ==> _module.__default.SubstSeq#canCall(Lit(parent#0), Seq#Take(Lit(q#0), Seq#Length(Lit(q#0)) - 1), v#0, val#0)
             && _module.__default.Substitute#canCall($Unbox(Seq#Index(Lit(q#0), Seq#Length(Lit(q#0)) - 1)): DatatypeType, v#0, val#0))
         && _module.__default.SubstSeq($LS($ly), Lit(parent#0), Lit(q#0), v#0, val#0)
           == (if Seq#Equal(q#0, Seq#Empty(): Seq Box)
             then Seq#Empty(): Seq Box
             else Seq#Append(_module.__default.SubstSeq($LS($ly), 
                Lit(parent#0), 
                Seq#Take(Lit(q#0), Seq#Length(Lit(q#0)) - 1), 
                v#0, 
                val#0), 
              Seq#Build(Seq#Empty(): Seq Box, 
                $Box(_module.__default.Substitute($LS($ly), 
                    $Unbox(Seq#Index(Lit(q#0), Seq#Length(Lit(q#0)) - 1)): DatatypeType, 
                    v#0, 
                    val#0))))));

// definition axiom for _module.__default.SubstSeq for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int :: 
    {:weight 3} { _module.__default.SubstSeq($LS($ly), Lit(parent#0), Lit(q#0), LitInt(v#0), LitInt(val#0)) } 
    _module.__default.SubstSeq#canCall(Lit(parent#0), Lit(q#0), LitInt(v#0), LitInt(val#0))
         || (4 != $FunctionContextHeight
           && 
          $Is(parent#0, Tclass._module.Expression())
           && $Is(q#0, TSeq(Tclass._module.Expression()))
           && (forall a#3: DatatypeType :: 
            { Seq#Contains(q#0, $Box(a#3)) } 
            $Is(a#3, Tclass._module.Expression())
               ==> 
              Seq#Contains(q#0, $Box(a#3))
               ==> DtRank(a#3) < DtRank(parent#0)))
       ==> (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
           ==> _module.__default.SubstSeq#canCall(Lit(parent#0), 
              Seq#Take(Lit(q#0), Seq#Length(Lit(q#0)) - 1), 
              LitInt(v#0), 
              LitInt(val#0))
             && _module.__default.Substitute#canCall($Unbox(Seq#Index(Lit(q#0), Seq#Length(Lit(q#0)) - 1)): DatatypeType, 
              LitInt(v#0), 
              LitInt(val#0)))
         && _module.__default.SubstSeq($LS($ly), Lit(parent#0), Lit(q#0), LitInt(v#0), LitInt(val#0))
           == (if Seq#Equal(q#0, Seq#Empty(): Seq Box)
             then Seq#Empty(): Seq Box
             else Seq#Append(_module.__default.SubstSeq($LS($ly), 
                Lit(parent#0), 
                Seq#Take(Lit(q#0), Seq#Length(Lit(q#0)) - 1), 
                LitInt(v#0), 
                LitInt(val#0)), 
              Seq#Build(Seq#Empty(): Seq Box, 
                $Box(_module.__default.Substitute($LS($ly), 
                    $Unbox(Seq#Index(Lit(q#0), Seq#Length(Lit(q#0)) - 1)): DatatypeType, 
                    LitInt(v#0), 
                    LitInt(val#0)))))));

procedure CheckWellformed$$_module.__default.SubstSeq(parent#0: DatatypeType where $Is(parent#0, Tclass._module.Expression()), 
    q#0: Seq Box where $Is(q#0, TSeq(Tclass._module.Expression())), 
    v#0: int, 
    val#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SubstSeq(parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#4: DatatypeType;
  var ##parent#0: DatatypeType;
  var ##q#0: Seq Box;
  var ##v#0: int;
  var ##val#0: int;
  var ##e#0: DatatypeType;
  var ##v#1: int;
  var ##val#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function SubstSeq
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(64,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // Begin Comprehension WF check
    havoc a#4;
    if ($Is(a#4, Tclass._module.Expression()))
    {
        if (Seq#Contains(q#0, $Box(a#4)))
        {
        }
    }

    // End Comprehension WF check
    assume (forall a#5: DatatypeType :: 
      { Seq#Contains(q#0, $Box(a#5)) } 
      $Is(a#5, Tclass._module.Expression())
         ==> 
        Seq#Contains(q#0, $Box(a#5))
         ==> DtRank(a#5) < DtRank(parent#0));
    if (*)
    {
        assume $Is(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), 
          TSeq(Tclass._module.Expression()));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (Seq#Equal(q#0, Seq#Empty(): Seq Box))
        {
            assume _module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0)
               == Lit(Seq#Empty(): Seq Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), 
              TSeq(Tclass._module.Expression()));
        }
        else
        {
            assert 0 <= Seq#Length(q#0) - 1 && Seq#Length(q#0) - 1 <= Seq#Length(q#0);
            ##parent#0 := parent#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##parent#0, Tclass._module.Expression(), $Heap);
            ##q#0 := Seq#Take(q#0, Seq#Length(q#0) - 1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##q#0, TSeq(Tclass._module.Expression()), $Heap);
            ##v#0 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#0, TInt, $Heap);
            ##val#0 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#0, TInt, $Heap);
            assert {:subsumption 0} (forall a#6: DatatypeType :: 
              { Seq#Contains(##q#0, $Box(a#6)) } 
              $Is(a#6, Tclass._module.Expression())
                 ==> 
                Seq#Contains(##q#0, $Box(a#6))
                 ==> DtRank(a#6) < DtRank(##parent#0));
            assume (forall a#6: DatatypeType :: 
              { Seq#Contains(##q#0, $Box(a#6)) } 
              $Is(a#6, Tclass._module.Expression())
                 ==> 
                Seq#Contains(##q#0, $Box(a#6))
                 ==> DtRank(a#6) < DtRank(##parent#0));
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##parent#0) < DtRank(parent#0)
               || (DtRank(##parent#0) == DtRank(parent#0) && Seq#Rank(##q#0) < Seq#Rank(q#0));
            assume _module.__default.SubstSeq#canCall(parent#0, Seq#Take(q#0, Seq#Length(q#0) - 1), v#0, val#0);
            assert 0 <= Seq#Length(q#0) - 1 && Seq#Length(q#0) - 1 < Seq#Length(q#0);
            ##e#0 := $Unbox(Seq#Index(q#0, Seq#Length(q#0) - 1)): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#0, Tclass._module.Expression(), $Heap);
            ##v#1 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#1, TInt, $Heap);
            ##val#1 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#1, TInt, $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##e#0) < DtRank(parent#0);
            assume _module.__default.Substitute#canCall($Unbox(Seq#Index(q#0, Seq#Length(q#0) - 1)): DatatypeType, v#0, val#0);
            assume _module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0)
               == Seq#Append(_module.__default.SubstSeq($LS($LZ), parent#0, Seq#Take(q#0, Seq#Length(q#0) - 1), v#0, val#0), 
                Seq#Build(Seq#Empty(): Seq Box, 
                  $Box(_module.__default.Substitute($LS($LZ), $Unbox(Seq#Index(q#0, Seq#Length(q#0) - 1)): DatatypeType, v#0, val#0))));
            assume _module.__default.SubstSeq#canCall(parent#0, Seq#Take(q#0, Seq#Length(q#0) - 1), v#0, val#0)
               && _module.__default.Substitute#canCall($Unbox(Seq#Index(q#0, Seq#Length(q#0) - 1)): DatatypeType, v#0, val#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), 
              TSeq(Tclass._module.Expression()));
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure {:_induction e#0, v#0, val#0} CheckWellformed$$_module.__default.TheoremSeq(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Expression())
         && $IsAlloc(e#0, Tclass._module.Expression(), $Heap)
         && $IsA#_module.Expression(e#0), 
    v#0: int, 
    val#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction e#0, v#0, val#0} Call$$_module.__default.TheoremSeq(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Expression())
         && $IsAlloc(e#0, Tclass._module.Expression(), $Heap)
         && $IsA#_module.Expression(e#0), 
    v#0: int, 
    val#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Expression(_module.__default.Substitute($LS($LZ), _module.__default.Substitute($LS($LZ), e#0, v#0, val#0), v#0, val#0))
     && $IsA#_module.Expression(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0))
     && 
    _module.__default.Substitute#canCall(e#0, v#0, val#0)
     && _module.__default.Substitute#canCall(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0), v#0, val#0)
     && _module.__default.Substitute#canCall(e#0, v#0, val#0);
  ensures _module.Expression#Equal(_module.__default.Substitute($LS($LS($LZ)), 
      _module.__default.Substitute($LS($LS($LZ)), e#0, v#0, val#0), 
      v#0, 
      val#0), 
    _module.__default.Substitute($LS($LS($LZ)), e#0, v#0, val#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction e#0, v#0, val#0} Impl$$_module.__default.TheoremSeq(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Expression())
         && $IsAlloc(e#0, Tclass._module.Expression(), $Heap)
         && $IsA#_module.Expression(e#0), 
    v#0: int, 
    val#0: int)
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Expression(_module.__default.Substitute($LS($LZ), _module.__default.Substitute($LS($LZ), e#0, v#0, val#0), v#0, val#0))
     && $IsA#_module.Expression(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0))
     && 
    _module.__default.Substitute#canCall(e#0, v#0, val#0)
     && _module.__default.Substitute#canCall(_module.__default.Substitute($LS($LZ), e#0, v#0, val#0), v#0, val#0)
     && _module.__default.Substitute#canCall(e#0, v#0, val#0);
  ensures _module.Expression#Equal(_module.__default.Substitute($LS($LS($LZ)), 
      _module.__default.Substitute($LS($LS($LZ)), e#0, v#0, val#0), 
      v#0, 
      val#0), 
    _module.__default.Substitute($LS($LS($LZ)), e#0, v#0, val#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction e#0, v#0, val#0} Impl$$_module.__default.TheoremSeq(e#0: DatatypeType, v#0: int, val#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#2#0_0: int;
  var _mcc#3#0_0: Seq Box;
  var args#0_0: Seq Box;
  var let#0_0#0#0: Seq Box;
  var op#0_0: int;
  var let#0_1#0#0: int;
  var seArgs#0_0: Seq Box
     where $Is(seArgs#0_0, TSeq(Tclass._module.Expression()))
       && $IsAlloc(seArgs#0_0, TSeq(Tclass._module.Expression()), $Heap);
  var ##parent#0_0: DatatypeType;
  var ##q#0_0: Seq Box;
  var ##v#0_0: int;
  var ##val#0_0: int;
  var parent##0_0: DatatypeType;
  var q##0_0: Seq Box;
  var v##0_0: int;
  var val##0_0: int;
  var se#0_0: DatatypeType
     where $Is(se#0_0, Tclass._module.Expression())
       && $IsAlloc(se#0_0, Tclass._module.Expression(), $Heap);
  var ##e#0_0: DatatypeType;
  var ##v#0_1: int;
  var ##val#0_1: int;
  var seArgs2#0_0: Seq Box
     where $Is(seArgs2#0_0, TSeq(Tclass._module.Expression()))
       && $IsAlloc(seArgs2#0_0, TSeq(Tclass._module.Expression()), $Heap);
  var ##parent#0_1: DatatypeType;
  var ##q#0_1: Seq Box;
  var ##v#0_2: int;
  var ##val#0_2: int;
  var parent##0_1: DatatypeType;
  var q##0_1: Seq Box;
  var v##0_1: int;
  var val##0_1: int;
  var N#0_0: int;
  var j#0_0: int;
  var $PreLoopHeap$loop#0_0: Heap;
  var $decr_init$loop#0_00: int;
  var $w$loop#0_0: bool;
  var k#0_0: int;
  var $decr$loop#0_00: int;
  var e##0_0_0: DatatypeType;
  var v##0_0_0: int;
  var val##0_0_0: int;
  var _mcc#1#1_0: int;
  var x#1_0: int;
  var let#1_0#0#0: int;
  var _mcc#0#2_0: int;
  var c#2_0: int;
  var let#2_0#0#0: int;

    // AddMethodImpl: TheoremSeq, Impl$$_module.__default.TheoremSeq
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(75,0): initial state"} true;
    assume $IsA#_module.Expression(e#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#e0#0: DatatypeType, $ih#v0#0: int, $ih#val0#0: int :: 
      $Is($ih#e0#0, Tclass._module.Expression())
           && Lit(true)
           && (DtRank($ih#e0#0) < DtRank(e#0)
             || (DtRank($ih#e0#0) == DtRank(e#0)
               && ((0 <= $ih#v0#0 && $ih#v0#0 < v#0)
                 || ($ih#v0#0 == v#0 && 0 <= $ih#val0#0 && $ih#val0#0 < val#0))))
         ==> _module.Expression#Equal(_module.__default.Substitute($LS($LZ), 
            _module.__default.Substitute($LS($LZ), $ih#e0#0, $ih#v0#0, $ih#val0#0), 
            $ih#v0#0, 
            $ih#val0#0), 
          _module.__default.Substitute($LS($LZ), $ih#e0#0, $ih#v0#0, $ih#val0#0)));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#2#0_0, _mcc#3#0_0;
    havoc _mcc#1#1_0;
    havoc _mcc#0#2_0;
    if (e#0 == #_module.Expression.Const(_mcc#0#2_0))
    {
        havoc c#2_0;
        assume let#2_0#0#0 == _mcc#0#2_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_0#0#0, TInt);
        assume c#2_0 == let#2_0#0#0;
    }
    else if (e#0 == #_module.Expression.Var(_mcc#1#1_0))
    {
        havoc x#1_0;
        assume let#1_0#0#0 == _mcc#1#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_0#0#0, TInt);
        assume x#1_0 == let#1_0#0#0;
    }
    else if (e#0 == #_module.Expression.Nary(_mcc#2#0_0, _mcc#3#0_0))
    {
        assume $Is(_mcc#3#0_0, TSeq(Tclass._module.Expression()));
        havoc args#0_0;
        assume $Is(args#0_0, TSeq(Tclass._module.Expression()))
           && $IsAlloc(args#0_0, TSeq(Tclass._module.Expression()), $Heap);
        assume let#0_0#0#0 == _mcc#3#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, TSeq(Tclass._module.Expression()));
        assume args#0_0 == let#0_0#0#0;
        havoc op#0_0;
        assume let#0_1#0#0 == _mcc#2#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume op#0_0 == let#0_1#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(80,24)
        assume true;
        ##parent#0_0 := e#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##parent#0_0, Tclass._module.Expression(), $Heap);
        ##q#0_0 := args#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##q#0_0, TSeq(Tclass._module.Expression()), $Heap);
        ##v#0_0 := v#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##v#0_0, TInt, $Heap);
        ##val#0_0 := val#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##val#0_0, TInt, $Heap);
        assert {:subsumption 0} (forall a#0_0: DatatypeType :: 
          { Seq#Contains(##q#0_0, $Box(a#0_0)) } 
          $Is(a#0_0, Tclass._module.Expression())
             ==> 
            Seq#Contains(##q#0_0, $Box(a#0_0))
             ==> DtRank(a#0_0) < DtRank(##parent#0_0));
        assume (forall a#0_0: DatatypeType :: 
          { Seq#Contains(##q#0_0, $Box(a#0_0)) } 
          $Is(a#0_0, Tclass._module.Expression())
             ==> 
            Seq#Contains(##q#0_0, $Box(a#0_0))
             ==> DtRank(a#0_0) < DtRank(##parent#0_0));
        assume _module.__default.SubstSeq#canCall(e#0, args#0_0, v#0, val#0);
        assume _module.__default.SubstSeq#canCall(e#0, args#0_0, v#0, val#0);
        seArgs#0_0 := _module.__default.SubstSeq($LS($LZ), e#0, args#0_0, v#0, val#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(80,51)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(81,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        parent##0_0 := e#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        q##0_0 := args#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0_0 := v#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0_0 := val#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LemmaSeq(parent##0_0, q##0_0, v##0_0, val##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(81,31)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(83,20)
        assume true;
        ##e#0_0 := e#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#0_0, Tclass._module.Expression(), $Heap);
        ##v#0_1 := v#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##v#0_1, TInt, $Heap);
        ##val#0_1 := val#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##val#0_1, TInt, $Heap);
        assume _module.__default.Substitute#canCall(e#0, v#0, val#0);
        assume _module.__default.Substitute#canCall(e#0, v#0, val#0);
        se#0_0 := _module.__default.Substitute($LS($LZ), e#0, v#0, val#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(83,43)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(84,25)
        assume true;
        ##parent#0_1 := se#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##parent#0_1, Tclass._module.Expression(), $Heap);
        ##q#0_1 := seArgs#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##q#0_1, TSeq(Tclass._module.Expression()), $Heap);
        ##v#0_2 := v#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##v#0_2, TInt, $Heap);
        ##val#0_2 := val#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##val#0_2, TInt, $Heap);
        assert {:subsumption 0} (forall a#0_1: DatatypeType :: 
          { Seq#Contains(##q#0_1, $Box(a#0_1)) } 
          $Is(a#0_1, Tclass._module.Expression())
             ==> 
            Seq#Contains(##q#0_1, $Box(a#0_1))
             ==> DtRank(a#0_1) < DtRank(##parent#0_1));
        assume (forall a#0_1: DatatypeType :: 
          { Seq#Contains(##q#0_1, $Box(a#0_1)) } 
          $Is(a#0_1, Tclass._module.Expression())
             ==> 
            Seq#Contains(##q#0_1, $Box(a#0_1))
             ==> DtRank(a#0_1) < DtRank(##parent#0_1));
        assume _module.__default.SubstSeq#canCall(se#0_0, seArgs#0_0, v#0, val#0);
        assume _module.__default.SubstSeq#canCall(se#0_0, seArgs#0_0, v#0, val#0);
        seArgs2#0_0 := _module.__default.SubstSeq($LS($LZ), se#0_0, seArgs#0_0, v#0, val#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(84,55)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(85,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        parent##0_1 := se#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        q##0_1 := seArgs#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0_1 := v#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0_1 := val#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LemmaSeq(parent##0_1, q##0_1, v##0_1, val##0_1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(85,34)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(87,13)
        assume true;
        assume true;
        N#0_0 := Seq#Length(args#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(87,21)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(88,13)
        assume true;
        assume true;
        j#0_0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(88,16)"} true;
        // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(89,7)
        // Assume Fuel Constant
        $PreLoopHeap$loop#0_0 := $Heap;
        $decr_init$loop#0_00 := N#0_0 - j#0_0;
        havoc $w$loop#0_0;
        while (true)
          free invariant $w$loop#0_0 ==> true;
          invariant $w$loop#0_0 ==> j#0_0 <= N#0_0;
          free invariant $w$loop#0_0
             ==> (forall k#0_1: int :: 
              { $Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType } 
                { $Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType } 
              LitInt(0) <= k#0_1
                 ==> 
                k#0_1 < j#0_0
                 ==> $IsA#_module.Expression($Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType)
                   && $IsA#_module.Expression($Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType));
          invariant $w$loop#0_0
             ==> (forall k#0_1: int :: 
              { $Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType } 
                { $Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType } 
              true
                 ==> 
                LitInt(0) <= k#0_1 && k#0_1 < j#0_0
                 ==> _module.Expression#Equal($Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType, 
                  $Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType));
          free invariant $PreLoopHeap$loop#0_0 == $Heap;
          free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
            { read($Heap, $o, $f) } 
            $o != null && read($PreLoopHeap$loop#0_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0_0, $o, $f) || $_Frame[$o, $f]);
          free invariant N#0_0 - j#0_0 <= $decr_init$loop#0_00
             && (N#0_0 - j#0_0 == $decr_init$loop#0_00 ==> true);
        {
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(89,6): after some loop iterations"} true;
            if (!$w$loop#0_0)
            {
                assume true;
                assume j#0_0 <= N#0_0;
                // Begin Comprehension WF check
                havoc k#0_0;
                if (true)
                {
                    if (LitInt(0) <= k#0_0)
                    {
                    }

                    if (LitInt(0) <= k#0_0 && k#0_0 < j#0_0)
                    {
                        assert {:subsumption 0} 0 <= k#0_0 && k#0_0 < Seq#Length(seArgs2#0_0);
                        assert {:subsumption 0} 0 <= k#0_0 && k#0_0 < Seq#Length(seArgs#0_0);
                    }
                }

                // End Comprehension WF check
                assume (forall k#0_1: int :: 
                  { $Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType } 
                    { $Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType } 
                  LitInt(0) <= k#0_1
                     ==> 
                    k#0_1 < j#0_0
                     ==> $IsA#_module.Expression($Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType)
                       && $IsA#_module.Expression($Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType));
                assume (forall k#0_1: int :: 
                  { $Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType } 
                    { $Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType } 
                  true
                     ==> 
                    LitInt(0) <= k#0_1 && k#0_1 < j#0_0
                     ==> _module.Expression#Equal($Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType, 
                      $Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType));
                assume true;
                assume false;
            }

            assume true;
            if (N#0_0 <= j#0_0)
            {
                break;
            }

            $decr$loop#0_00 := N#0_0 - j#0_0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(93,19)
            // TrCallStmt: Before ProcessCallStmt
            assert 0 <= j#0_0 && j#0_0 < Seq#Length(args#0_0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            e##0_0_0 := $Unbox(Seq#Index(args#0_0, j#0_0)): DatatypeType;
            assume true;
            // ProcessCallStmt: CheckSubrange
            v##0_0_0 := v#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            val##0_0_0 := val#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= v#0 || DtRank(e##0_0_0) < DtRank(e#0) || v##0_0_0 == v#0;
            assert 0 <= val#0
               || DtRank(e##0_0_0) < DtRank(e#0)
               || v##0_0_0 < v#0
               || val##0_0_0 == val#0;
            assert DtRank(e##0_0_0) < DtRank(e#0)
               || (DtRank(e##0_0_0) == DtRank(e#0)
                 && (v##0_0_0 < v#0 || (v##0_0_0 == v#0 && val##0_0_0 < val#0)));
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.TheoremSeq(e##0_0_0, v##0_0_0, val##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(93,35)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(94,11)
            assume true;
            assume true;
            j#0_0 := j#0_0 + 1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(94,18)"} true;
            // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(89,7)
            assert 0 <= $decr$loop#0_00 || N#0_0 - j#0_0 == $decr$loop#0_00;
            assert N#0_0 - j#0_0 < $decr$loop#0_00;
            assume true;
            assume (forall k#0_1: int :: 
              { $Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType } 
                { $Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType } 
              LitInt(0) <= k#0_1
                 ==> 
                k#0_1 < j#0_0
                 ==> $IsA#_module.Expression($Unbox(Seq#Index(seArgs2#0_0, k#0_1)): DatatypeType)
                   && $IsA#_module.Expression($Unbox(Seq#Index(seArgs#0_0, k#0_1)): DatatypeType));
        }

        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(96,7)
        assume true;
        assert Seq#Equal(seArgs#0_0, seArgs2#0_0);
    }
    else
    {
        assume false;
    }
}



procedure {:_induction parent#0, q#0, v#0, val#0} CheckWellformed$$_module.__default.LemmaSeq(parent#0: DatatypeType
       where $Is(parent#0, Tclass._module.Expression())
         && $IsAlloc(parent#0, Tclass._module.Expression(), $Heap)
         && $IsA#_module.Expression(parent#0), 
    q#0: Seq Box
       where $Is(q#0, TSeq(Tclass._module.Expression()))
         && $IsAlloc(q#0, TSeq(Tclass._module.Expression()), $Heap), 
    v#0: int, 
    val#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction parent#0, q#0, v#0, val#0} CheckWellformed$$_module.__default.LemmaSeq(parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: DatatypeType;
  var ##parent#0: DatatypeType;
  var ##q#0: Seq Box;
  var ##v#0: int;
  var ##val#0: int;
  var k#0: int;
  var ##parent#1: DatatypeType;
  var ##q#1: Seq Box;
  var ##v#1: int;
  var ##val#1: int;
  var ##e#0: DatatypeType;
  var ##v#2: int;
  var ##val#2: int;

    // AddMethodImpl: LemmaSeq, CheckWellformed$$_module.__default.LemmaSeq
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(100,6): initial state"} true;
    // Begin Comprehension WF check
    havoc a#0;
    if ($Is(a#0, Tclass._module.Expression()))
    {
        if (Seq#Contains(q#0, $Box(a#0)))
        {
        }
    }

    // End Comprehension WF check
    assume (forall a#1: DatatypeType :: 
      { Seq#Contains(q#0, $Box(a#1)) } 
      $Is(a#1, Tclass._module.Expression())
         ==> 
        Seq#Contains(q#0, $Box(a#1))
         ==> DtRank(a#1) < DtRank(parent#0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(102,40): post-state"} true;
    ##parent#0 := parent#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##parent#0, Tclass._module.Expression(), $Heap);
    ##q#0 := q#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##q#0, TSeq(Tclass._module.Expression()), $Heap);
    ##v#0 := v#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##v#0, TInt, $Heap);
    ##val#0 := val#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##val#0, TInt, $Heap);
    assert {:subsumption 0} (forall a#2: DatatypeType :: 
      { Seq#Contains(##q#0, $Box(a#2)) } 
      $Is(a#2, Tclass._module.Expression())
         ==> 
        Seq#Contains(##q#0, $Box(a#2))
         ==> DtRank(a#2) < DtRank(##parent#0));
    assume (forall a#2: DatatypeType :: 
      { Seq#Contains(##q#0, $Box(a#2)) } 
      $Is(a#2, Tclass._module.Expression())
         ==> 
        Seq#Contains(##q#0, $Box(a#2))
         ==> DtRank(a#2) < DtRank(##parent#0));
    assume _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0);
    assume Seq#Length(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0))
       == Seq#Length(q#0);
    // Begin Comprehension WF check
    havoc k#0;
    if (true)
    {
        if (LitInt(0) <= k#0)
        {
        }

        if (LitInt(0) <= k#0 && k#0 < Seq#Length(q#0))
        {
            ##parent#1 := parent#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##parent#1, Tclass._module.Expression(), $Heap);
            ##q#1 := q#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##q#1, TSeq(Tclass._module.Expression()), $Heap);
            ##v#1 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#1, TInt, $Heap);
            ##val#1 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#1, TInt, $Heap);
            assert {:subsumption 0} (forall a#3: DatatypeType :: 
              { Seq#Contains(##q#1, $Box(a#3)) } 
              $Is(a#3, Tclass._module.Expression())
                 ==> 
                Seq#Contains(##q#1, $Box(a#3))
                 ==> DtRank(a#3) < DtRank(##parent#1));
            assume (forall a#3: DatatypeType :: 
              { Seq#Contains(##q#1, $Box(a#3)) } 
              $Is(a#3, Tclass._module.Expression())
                 ==> 
                Seq#Contains(##q#1, $Box(a#3))
                 ==> DtRank(a#3) < DtRank(##parent#1));
            assume _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0);
            assert 0 <= k#0
               && k#0
                 < Seq#Length(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0));
            assert 0 <= k#0 && k#0 < Seq#Length(q#0);
            ##e#0 := $Unbox(Seq#Index(q#0, k#0)): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#0, Tclass._module.Expression(), $Heap);
            ##v#2 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##v#2, TInt, $Heap);
            ##val#2 := val#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#2, TInt, $Heap);
            assume _module.__default.Substitute#canCall($Unbox(Seq#Index(q#0, k#0)): DatatypeType, v#0, val#0);
        }
    }

    // End Comprehension WF check
    assume (forall k#1: int :: 
      { $Unbox(Seq#Index(q#0, k#1)): DatatypeType } 
        { $Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType } 
      true
         ==> 
        LitInt(0) <= k#1 && k#1 < Seq#Length(q#0)
         ==> _module.Expression#Equal($Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType, 
          _module.__default.Substitute($LS($LZ), $Unbox(Seq#Index(q#0, k#1)): DatatypeType, v#0, val#0)));
}



procedure {:_induction parent#0, q#0, v#0, val#0} Call$$_module.__default.LemmaSeq(parent#0: DatatypeType
       where $Is(parent#0, Tclass._module.Expression())
         && $IsAlloc(parent#0, Tclass._module.Expression(), $Heap)
         && $IsA#_module.Expression(parent#0), 
    q#0: Seq Box
       where $Is(q#0, TSeq(Tclass._module.Expression()))
         && $IsAlloc(q#0, TSeq(Tclass._module.Expression()), $Heap), 
    v#0: int, 
    val#0: int);
  // user-defined preconditions
  requires (forall a#1: DatatypeType :: 
    { Seq#Contains(q#0, $Box(a#1)) } 
    $Is(a#1, Tclass._module.Expression())
       ==> 
      Seq#Contains(q#0, $Box(a#1))
       ==> DtRank(a#1) < DtRank(parent#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0);
  ensures Seq#Length(_module.__default.SubstSeq($LS($LS($LZ)), parent#0, q#0, v#0, val#0))
     == Seq#Length(q#0);
  free ensures (forall k#1: int :: 
    { $Unbox(Seq#Index(q#0, k#1)): DatatypeType } 
      { $Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType } 
    LitInt(0) <= k#1
       ==> 
      k#1 < Seq#Length(q#0)
       ==> $IsA#_module.Expression($Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType)
         && $IsA#_module.Expression(_module.__default.Substitute($LS($LZ), $Unbox(Seq#Index(q#0, k#1)): DatatypeType, v#0, val#0))
         && 
        _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0)
         && _module.__default.Substitute#canCall($Unbox(Seq#Index(q#0, k#1)): DatatypeType, v#0, val#0));
  free ensures (forall k#1: int :: 
    { $Unbox(Seq#Index(q#0, k#1)): DatatypeType } 
      { $Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType } 
    true
       ==> 
      LitInt(0) <= k#1 && k#1 < Seq#Length(q#0)
       ==> _module.Expression#Equal($Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType, 
        _module.__default.Substitute($LS($LZ), $Unbox(Seq#Index(q#0, k#1)): DatatypeType, v#0, val#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction parent#0, q#0, v#0, val#0} Impl$$_module.__default.LemmaSeq(parent#0: DatatypeType
       where $Is(parent#0, Tclass._module.Expression())
         && $IsAlloc(parent#0, Tclass._module.Expression(), $Heap)
         && $IsA#_module.Expression(parent#0), 
    q#0: Seq Box
       where $Is(q#0, TSeq(Tclass._module.Expression()))
         && $IsAlloc(q#0, TSeq(Tclass._module.Expression()), $Heap), 
    v#0: int, 
    val#0: int)
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall a#1: DatatypeType :: 
    { Seq#Contains(q#0, $Box(a#1)) } 
    $Is(a#1, Tclass._module.Expression())
       ==> 
      Seq#Contains(q#0, $Box(a#1))
       ==> DtRank(a#1) < DtRank(parent#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0);
  ensures Seq#Length(_module.__default.SubstSeq($LS($LS($LZ)), parent#0, q#0, v#0, val#0))
     == Seq#Length(q#0);
  free ensures (forall k#1: int :: 
    { $Unbox(Seq#Index(q#0, k#1)): DatatypeType } 
      { $Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType } 
    LitInt(0) <= k#1
       ==> 
      k#1 < Seq#Length(q#0)
       ==> $IsA#_module.Expression($Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), parent#0, q#0, v#0, val#0), k#1)): DatatypeType)
         && $IsA#_module.Expression(_module.__default.Substitute($LS($LZ), $Unbox(Seq#Index(q#0, k#1)): DatatypeType, v#0, val#0))
         && 
        _module.__default.SubstSeq#canCall(parent#0, q#0, v#0, val#0)
         && _module.__default.Substitute#canCall($Unbox(Seq#Index(q#0, k#1)): DatatypeType, v#0, val#0));
  ensures (forall k#1: int :: 
    { $Unbox(Seq#Index(q#0, k#1)): DatatypeType } 
      { $Unbox(Seq#Index(_module.__default.SubstSeq($LS($LS($LZ)), parent#0, q#0, v#0, val#0), k#1)): DatatypeType } 
    true
       ==> 
      LitInt(0) <= k#1 && k#1 < Seq#Length(q#0)
       ==> _module.Expression#Equal($Unbox(Seq#Index(_module.__default.SubstSeq($LS($LS($LZ)), parent#0, q#0, v#0, val#0), k#1)): DatatypeType, 
        _module.__default.Substitute($LS($LS($LZ)), $Unbox(Seq#Index(q#0, k#1)): DatatypeType, v#0, val#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction parent#0, q#0, v#0, val#0} Impl$$_module.__default.LemmaSeq(parent#0: DatatypeType, q#0: Seq Box, v#0: int, val#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var parent##0: DatatypeType;
  var q##0: Seq Box;
  var v##0: int;
  var val##0: int;

    // AddMethodImpl: LemmaSeq, Impl$$_module.__default.LemmaSeq
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(105,0): initial state"} true;
    assume $IsA#_module.Expression(parent#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#parent0#0: DatatypeType, $ih#q0#0: Seq Box, $ih#v0#0: int, $ih#val0#0: int :: 
      $Is($ih#parent0#0, Tclass._module.Expression())
           && $Is($ih#q0#0, TSeq(Tclass._module.Expression()))
           && (forall a#4: DatatypeType :: 
            { Seq#Contains($ih#q0#0, $Box(a#4)) } 
            $Is(a#4, Tclass._module.Expression())
               ==> 
              Seq#Contains($ih#q0#0, $Box(a#4))
               ==> DtRank(a#4) < DtRank($ih#parent0#0))
           && (DtRank($ih#parent0#0) < DtRank(parent#0)
             || (DtRank($ih#parent0#0) == DtRank(parent#0)
               && (Seq#Rank($ih#q0#0) < Seq#Rank(q#0)
                 || (Seq#Rank($ih#q0#0) == Seq#Rank(q#0)
                   && ((0 <= $ih#v0#0 && $ih#v0#0 < v#0)
                     || ($ih#v0#0 == v#0 && 0 <= $ih#val0#0 && $ih#val0#0 < val#0))))))
         ==> Seq#Length(_module.__default.SubstSeq($LS($LZ), $ih#parent0#0, $ih#q0#0, $ih#v0#0, $ih#val0#0))
             == Seq#Length($ih#q0#0)
           && (forall k#2: int :: 
            { $Unbox(Seq#Index($ih#q0#0, k#2)): DatatypeType } 
              { $Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), $ih#parent0#0, $ih#q0#0, $ih#v0#0, $ih#val0#0), 
                  k#2)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= k#2 && k#2 < Seq#Length($ih#q0#0)
               ==> _module.Expression#Equal($Unbox(Seq#Index(_module.__default.SubstSeq($LS($LZ), $ih#parent0#0, $ih#q0#0, $ih#v0#0, $ih#val0#0), 
                    k#2)): DatatypeType, 
                _module.__default.Substitute($LS($LZ), $Unbox(Seq#Index($ih#q0#0, k#2)): DatatypeType, $ih#v0#0, $ih#val0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(106,3)
    assume true;
    if (Seq#Equal(q#0, Seq#Empty(): Seq Box))
    {
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(108,13)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        parent##0 := parent#0;
        assert 0 <= Seq#Length(q#0) - 1 && Seq#Length(q#0) - 1 <= Seq#Length(q#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        q##0 := Seq#Take(q#0, Seq#Length(q#0) - 1);
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0 := v#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0 := val#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= v#0
           || DtRank(parent##0) < DtRank(parent#0)
           || Seq#Rank(q##0) < Seq#Rank(q#0)
           || v##0 == v#0;
        assert 0 <= val#0
           || DtRank(parent##0) < DtRank(parent#0)
           || Seq#Rank(q##0) < Seq#Rank(q#0)
           || v##0 < v#0
           || val##0 == val#0;
        assert DtRank(parent##0) < DtRank(parent#0)
           || (DtRank(parent##0) == DtRank(parent#0)
             && (Seq#Rank(q##0) < Seq#Rank(q#0)
               || (Seq#Rank(q##0) == Seq#Rank(q#0)
                 && (v##0 < v#0 || (v##0 == v#0 && val##0 < val#0)))));
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LemmaSeq(parent##0, q##0, v##0, val##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Substitution.dfy(108,40)"} true;
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

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Expr: TyTagFamily;

const unique tytagFamily$Expression: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
