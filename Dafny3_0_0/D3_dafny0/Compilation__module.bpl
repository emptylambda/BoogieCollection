// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy -print:./Compilation.bpl

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

const BaseFuel__module._default.hidden: LayerType;

const StartFuel__module._default.hidden: LayerType;

const StartFuelAssert__module._default.hidden: LayerType;

// Constructor function declaration
function #_module.Tuple.Pair(Box, Box, int, int) : DatatypeType;

const unique ##_module.Tuple.Pair: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: Box, a#14#2#0: int, a#14#3#0: int :: 
  { #_module.Tuple.Pair(a#14#0#0, a#14#1#0, a#14#2#0, a#14#3#0) } 
  DatatypeCtorId(#_module.Tuple.Pair(a#14#0#0, a#14#1#0, a#14#2#0, a#14#3#0))
     == ##_module.Tuple.Pair);

function _module.Tuple.Pair_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Tuple.Pair_q(d) } 
  _module.Tuple.Pair_q(d) <==> DatatypeCtorId(d) == ##_module.Tuple.Pair);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Tuple.Pair_q(d) } 
  _module.Tuple.Pair_q(d)
     ==> (exists a#15#0#0: Box, a#15#1#0: Box, a#15#2#0: int, a#15#3#0: int :: 
      d == #_module.Tuple.Pair(a#15#0#0, a#15#1#0, a#15#2#0, a#15#3#0)));

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
axiom (forall _module.Tuple$T: Ty, 
    _module.Tuple$U: Ty, 
    a#16#0#0: Box, 
    a#16#1#0: Box, 
    a#16#2#0: int, 
    a#16#3#0: int :: 
  { $Is(#_module.Tuple.Pair(a#16#0#0, a#16#1#0, a#16#2#0, a#16#3#0), 
      Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U)) } 
  $Is(#_module.Tuple.Pair(a#16#0#0, a#16#1#0, a#16#2#0, a#16#3#0), 
      Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
     <==> $IsBox(a#16#0#0, _module.Tuple$T)
       && $IsBox(a#16#1#0, _module.Tuple$U)
       && $Is(a#16#2#0, TInt)
       && $Is(a#16#3#0, TInt));

// Constructor $IsAlloc
axiom (forall _module.Tuple$T: Ty, 
    _module.Tuple$U: Ty, 
    a#17#0#0: Box, 
    a#17#1#0: Box, 
    a#17#2#0: int, 
    a#17#3#0: int, 
    $h: Heap :: 
  { $IsAlloc(#_module.Tuple.Pair(a#17#0#0, a#17#1#0, a#17#2#0, a#17#3#0), 
      Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Tuple.Pair(a#17#0#0, a#17#1#0, a#17#2#0, a#17#3#0), 
        Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), 
        $h)
       <==> $IsAllocBox(a#17#0#0, _module.Tuple$T, $h)
         && $IsAllocBox(a#17#1#0, _module.Tuple$U, $h)
         && $IsAlloc(a#17#2#0, TInt, $h)
         && $IsAlloc(a#17#3#0, TInt, $h)));

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

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tuple.r(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tuple.Pair_q(d)
       && (exists _module.Tuple$T: Ty, _module.Tuple$U: Ty :: 
        { $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h) } 
        $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h))
     ==> $IsAlloc(_module.Tuple.r(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tuple.s_k(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tuple.Pair_q(d)
       && (exists _module.Tuple$T: Ty, _module.Tuple$U: Ty :: 
        { $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h) } 
        $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h))
     ==> $IsAlloc(_module.Tuple.s_k(d), TInt, $h));

// Constructor literal
axiom (forall a#18#0#0: Box, a#18#1#0: Box, a#18#2#0: int, a#18#3#0: int :: 
  { #_module.Tuple.Pair(Lit(a#18#0#0), Lit(a#18#1#0), LitInt(a#18#2#0), LitInt(a#18#3#0)) } 
  #_module.Tuple.Pair(Lit(a#18#0#0), Lit(a#18#1#0), LitInt(a#18#2#0), LitInt(a#18#3#0))
     == Lit(#_module.Tuple.Pair(a#18#0#0, a#18#1#0, a#18#2#0, a#18#3#0)));

function _module.Tuple._0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: Box, a#19#2#0: int, a#19#3#0: int :: 
  { #_module.Tuple.Pair(a#19#0#0, a#19#1#0, a#19#2#0, a#19#3#0) } 
  _module.Tuple._0(#_module.Tuple.Pair(a#19#0#0, a#19#1#0, a#19#2#0, a#19#3#0))
     == a#19#0#0);

// Inductive rank
axiom (forall a#20#0#0: Box, a#20#1#0: Box, a#20#2#0: int, a#20#3#0: int :: 
  { #_module.Tuple.Pair(a#20#0#0, a#20#1#0, a#20#2#0, a#20#3#0) } 
  BoxRank(a#20#0#0)
     < DtRank(#_module.Tuple.Pair(a#20#0#0, a#20#1#0, a#20#2#0, a#20#3#0)));

function _module.Tuple._1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#21#0#0: Box, a#21#1#0: Box, a#21#2#0: int, a#21#3#0: int :: 
  { #_module.Tuple.Pair(a#21#0#0, a#21#1#0, a#21#2#0, a#21#3#0) } 
  _module.Tuple._1(#_module.Tuple.Pair(a#21#0#0, a#21#1#0, a#21#2#0, a#21#3#0))
     == a#21#1#0);

// Inductive rank
axiom (forall a#22#0#0: Box, a#22#1#0: Box, a#22#2#0: int, a#22#3#0: int :: 
  { #_module.Tuple.Pair(a#22#0#0, a#22#1#0, a#22#2#0, a#22#3#0) } 
  BoxRank(a#22#1#0)
     < DtRank(#_module.Tuple.Pair(a#22#0#0, a#22#1#0, a#22#2#0, a#22#3#0)));

function _module.Tuple.r(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#23#0#0: Box, a#23#1#0: Box, a#23#2#0: int, a#23#3#0: int :: 
  { #_module.Tuple.Pair(a#23#0#0, a#23#1#0, a#23#2#0, a#23#3#0) } 
  _module.Tuple.r(#_module.Tuple.Pair(a#23#0#0, a#23#1#0, a#23#2#0, a#23#3#0))
     == a#23#2#0);

function _module.Tuple.s_k(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#24#0#0: Box, a#24#1#0: Box, a#24#2#0: int, a#24#3#0: int :: 
  { #_module.Tuple.Pair(a#24#0#0, a#24#1#0, a#24#2#0, a#24#3#0) } 
  _module.Tuple.s_k(#_module.Tuple.Pair(a#24#0#0, a#24#1#0, a#24#2#0, a#24#3#0))
     == a#24#3#0);

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
         && _module.Tuple._1(a) == _module.Tuple._1(b)
         && _module.Tuple.r(a) == _module.Tuple.r(b)
         && _module.Tuple.s_k(a) == _module.Tuple.s_k(b)));

// Datatype extensionality axiom: _module.Tuple
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tuple#Equal(a, b) } 
  _module.Tuple#Equal(a, b) <==> a == b);

const unique class._module.Tuple: ClassName;

const unique class._module.DigitsClass?: ClassName;

function Tclass._module.DigitsClass?() : Ty;

const unique Tagclass._module.DigitsClass?: TyTag;

// Tclass._module.DigitsClass? Tag
axiom Tag(Tclass._module.DigitsClass?()) == Tagclass._module.DigitsClass?
   && TagFamily(Tclass._module.DigitsClass?()) == tytagFamily$DigitsClass;

// Box/unbox axiom for Tclass._module.DigitsClass?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DigitsClass?()) } 
  $IsBox(bx, Tclass._module.DigitsClass?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DigitsClass?()));

// DigitsClass: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.DigitsClass?()) } 
  $Is($o, Tclass._module.DigitsClass?())
     <==> $o == null || dtype($o) == Tclass._module.DigitsClass?());

// DigitsClass: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.DigitsClass?(), $h) } 
  $IsAlloc($o, Tclass._module.DigitsClass?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.DigitsClass._7) == 0
   && FieldOfDecl(class._module.DigitsClass?, field$7) == _module.DigitsClass._7
   && !$IsGhostField(_module.DigitsClass._7);

const _module.DigitsClass._7: Field bool;

// DigitsClass.7: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitsClass._7) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.DigitsClass?()
     ==> $Is(read($h, $o, _module.DigitsClass._7), TBool));

// DigitsClass.7: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitsClass._7) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DigitsClass?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DigitsClass._7), TBool, $h));

function Tclass._module.DigitsClass() : Ty;

const unique Tagclass._module.DigitsClass: TyTag;

// Tclass._module.DigitsClass Tag
axiom Tag(Tclass._module.DigitsClass()) == Tagclass._module.DigitsClass
   && TagFamily(Tclass._module.DigitsClass()) == tytagFamily$DigitsClass;

// Box/unbox axiom for Tclass._module.DigitsClass
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DigitsClass()) } 
  $IsBox(bx, Tclass._module.DigitsClass())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DigitsClass()));

procedure CheckWellformed$$_module.DigitsClass.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitsClass())
         && $IsAlloc(this, Tclass._module.DigitsClass(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.DigitsClass())
         && $IsAlloc(c#0, Tclass._module.DigitsClass(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DigitsClass.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitsClass())
         && $IsAlloc(this, Tclass._module.DigitsClass(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.DigitsClass())
         && $IsAlloc(c#0, Tclass._module.DigitsClass(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.DigitsClass.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitsClass())
         && $IsAlloc(this, Tclass._module.DigitsClass(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.DigitsClass())
         && $IsAlloc(c#0, Tclass._module.DigitsClass(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.DigitsClass.M(this: ref, c#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;

    // AddMethodImpl: M, Impl$$_module.DigitsClass.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(183,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(184,16)
    assume true;
    if (read($Heap, this, _module.DigitsClass._7))
    {
    }
    else
    {
        assert c#0 != null;
        if (read($Heap, c#0, _module.DigitsClass._7))
        {
        }
        else
        {
        }
    }

    assume true;
    x#0 := (if read($Heap, this, _module.DigitsClass._7)
       then 7
       else (if read($Heap, c#0, _module.DigitsClass._7) then 8 else 9));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(184,60)"} true;
}



// _module.DigitsClass: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.DigitsClass()) } 
  $Is(c#0, Tclass._module.DigitsClass())
     <==> $Is(c#0, Tclass._module.DigitsClass?()) && c#0 != null);

// _module.DigitsClass: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.DigitsClass(), $h) } 
  $IsAlloc(c#0, Tclass._module.DigitsClass(), $h)
     <==> $IsAlloc(c#0, Tclass._module.DigitsClass?(), $h));

const unique class._module.DigitUnderscore__Names?: ClassName;

function Tclass._module.DigitUnderscore__Names?() : Ty;

const unique Tagclass._module.DigitUnderscore__Names?: TyTag;

// Tclass._module.DigitUnderscore__Names? Tag
axiom Tag(Tclass._module.DigitUnderscore__Names?())
     == Tagclass._module.DigitUnderscore__Names?
   && TagFamily(Tclass._module.DigitUnderscore__Names?())
     == tytagFamily$DigitUnderscore_Names;

// Box/unbox axiom for Tclass._module.DigitUnderscore__Names?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DigitUnderscore__Names?()) } 
  $IsBox(bx, Tclass._module.DigitUnderscore__Names?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DigitUnderscore__Names?()));

// DigitUnderscore_Names: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.DigitUnderscore__Names?()) } 
  $Is($o, Tclass._module.DigitUnderscore__Names?())
     <==> $o == null || dtype($o) == Tclass._module.DigitUnderscore__Names?());

// DigitUnderscore_Names: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.DigitUnderscore__Names?(), $h) } 
  $IsAlloc($o, Tclass._module.DigitUnderscore__Names?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.DigitUnderscore__Names._0_1_0) == 0
   && FieldOfDecl(class._module.DigitUnderscore__Names?, field$0_1_0)
     == _module.DigitUnderscore__Names._0_1_0
   && !$IsGhostField(_module.DigitUnderscore__Names._0_1_0);

const _module.DigitUnderscore__Names._0_1_0: Field int;

// DigitUnderscore_Names.0_1_0: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitUnderscore__Names._0_1_0) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DigitUnderscore__Names?()
     ==> $Is(read($h, $o, _module.DigitUnderscore__Names._0_1_0), TInt));

// DigitUnderscore_Names.0_1_0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitUnderscore__Names._0_1_0) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DigitUnderscore__Names?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DigitUnderscore__Names._0_1_0), TInt, $h));

axiom FDim(_module.DigitUnderscore__Names._010) == 0
   && FieldOfDecl(class._module.DigitUnderscore__Names?, field$010)
     == _module.DigitUnderscore__Names._010
   && !$IsGhostField(_module.DigitUnderscore__Names._010);

const _module.DigitUnderscore__Names._010: Field int;

// DigitUnderscore_Names.010: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitUnderscore__Names._010) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DigitUnderscore__Names?()
     ==> $Is(read($h, $o, _module.DigitUnderscore__Names._010), TInt));

// DigitUnderscore_Names.010: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitUnderscore__Names._010) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DigitUnderscore__Names?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DigitUnderscore__Names._010), TInt, $h));

axiom FDim(_module.DigitUnderscore__Names._10) == 0
   && FieldOfDecl(class._module.DigitUnderscore__Names?, field$10)
     == _module.DigitUnderscore__Names._10
   && !$IsGhostField(_module.DigitUnderscore__Names._10);

const _module.DigitUnderscore__Names._10: Field int;

// DigitUnderscore_Names.10: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitUnderscore__Names._10) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DigitUnderscore__Names?()
     ==> $Is(read($h, $o, _module.DigitUnderscore__Names._10), TInt));

// DigitUnderscore_Names.10: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DigitUnderscore__Names._10) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DigitUnderscore__Names?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DigitUnderscore__Names._10), TInt, $h));

function Tclass._module.DigitUnderscore__Names() : Ty;

const unique Tagclass._module.DigitUnderscore__Names: TyTag;

// Tclass._module.DigitUnderscore__Names Tag
axiom Tag(Tclass._module.DigitUnderscore__Names())
     == Tagclass._module.DigitUnderscore__Names
   && TagFamily(Tclass._module.DigitUnderscore__Names())
     == tytagFamily$DigitUnderscore_Names;

// Box/unbox axiom for Tclass._module.DigitUnderscore__Names
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DigitUnderscore__Names()) } 
  $IsBox(bx, Tclass._module.DigitUnderscore__Names())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DigitUnderscore__Names()));

procedure CheckWellformed$$_module.DigitUnderscore__Names.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names(), $Heap));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DigitUnderscore__Names.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.DigitUnderscore__Names.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.DigitUnderscore__Names.M(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var newtype$check#0: real;
  var $rhs#3: int;

    // AddMethodImpl: M, Impl$$_module.DigitUnderscore__Names.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(256,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(257,16)
    assume true;
    assert $_Frame[this, _module.DigitUnderscore__Names._0_1_0];
    assume true;
    $rhs#0 := LitInt(7);
    $Heap := update($Heap, this, _module.DigitUnderscore__Names._0_1_0, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(257,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(258,14)
    assume true;
    assert $_Frame[this, _module.DigitUnderscore__Names._010];
    assume true;
    $rhs#1 := LitInt(8);
    $Heap := update($Heap, this, _module.DigitUnderscore__Names._010, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(258,23)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(259,13)
    assume true;
    assert $_Frame[this, _module.DigitUnderscore__Names._10];
    assume true;
    $rhs#2 := LitInt(9);
    $Heap := update($Heap, this, _module.DigitUnderscore__Names._10, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(259,26)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(260,5)
    newtype$check#0 := LitReal(7e0);
    assert Real(Int(newtype$check#0)) == newtype$check#0;
    if (read($Heap, this, _module.DigitUnderscore__Names._0_1_0) == Int(LitReal(7e0)))
    {
    }

    if (read($Heap, this, _module.DigitUnderscore__Names._0_1_0) == Int(LitReal(7e0))
       && read($Heap, this, _module.DigitUnderscore__Names._010) == LitInt(8))
    {
    }

    assume true;
    assert {:subsumption 0} read($Heap, this, _module.DigitUnderscore__Names._0_1_0) == Int(LitReal(7e0));
    assert {:subsumption 0} read($Heap, this, _module.DigitUnderscore__Names._010) == LitInt(8);
    assert {:subsumption 0} read($Heap, this, _module.DigitUnderscore__Names._10) == LitInt(9);
    assume read($Heap, this, _module.DigitUnderscore__Names._0_1_0) == Int(LitReal(7e0))
       && read($Heap, this, _module.DigitUnderscore__Names._010) == LitInt(8)
       && read($Heap, this, _module.DigitUnderscore__Names._10) == LitInt(9);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(261,13)
    assume true;
    assert $_Frame[this, _module.DigitUnderscore__Names._10];
    assume true;
    $rhs#3 := LitInt(20);
    $Heap := update($Heap, this, _module.DigitUnderscore__Names._10, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(261,17)"} true;
}



// _module.DigitUnderscore_Names: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.DigitUnderscore__Names()) } 
  $Is(c#0, Tclass._module.DigitUnderscore__Names())
     <==> $Is(c#0, Tclass._module.DigitUnderscore__Names?()) && c#0 != null);

// _module.DigitUnderscore_Names: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.DigitUnderscore__Names(), $h) } 
  $IsAlloc(c#0, Tclass._module.DigitUnderscore__Names(), $h)
     <==> $IsAlloc(c#0, Tclass._module.DigitUnderscore__Names?(), $h));

const unique class._module.DigitUnderscore__Names__Functions__and__Methods?: ClassName;

function Tclass._module.DigitUnderscore__Names__Functions__and__Methods?() : Ty;

const unique Tagclass._module.DigitUnderscore__Names__Functions__and__Methods?: TyTag;

// Tclass._module.DigitUnderscore__Names__Functions__and__Methods? Tag
axiom Tag(Tclass._module.DigitUnderscore__Names__Functions__and__Methods?())
     == Tagclass._module.DigitUnderscore__Names__Functions__and__Methods?
   && TagFamily(Tclass._module.DigitUnderscore__Names__Functions__and__Methods?())
     == tytagFamily$DigitUnderscore_Names_Functions_and_Methods;

// Box/unbox axiom for Tclass._module.DigitUnderscore__Names__Functions__and__Methods?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?()) } 
  $IsBox(bx, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, 
        Tclass._module.DigitUnderscore__Names__Functions__and__Methods?()));

// DigitUnderscore_Names_Functions_and_Methods: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?()) } 
  $Is($o, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?())
     <==> $o == null
       || dtype($o) == Tclass._module.DigitUnderscore__Names__Functions__and__Methods?());

// DigitUnderscore_Names_Functions_and_Methods: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?(), $h) } 
  $IsAlloc($o, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module.DigitUnderscore_Names_Functions_and_Methods.70
function _module.DigitUnderscore__Names__Functions__and__Methods._70(this: ref) : int;

function _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(this: ref) : bool;

function Tclass._module.DigitUnderscore__Names__Functions__and__Methods() : Ty;

const unique Tagclass._module.DigitUnderscore__Names__Functions__and__Methods: TyTag;

// Tclass._module.DigitUnderscore__Names__Functions__and__Methods Tag
axiom Tag(Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
     == Tagclass._module.DigitUnderscore__Names__Functions__and__Methods
   && TagFamily(Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
     == tytagFamily$DigitUnderscore_Names_Functions_and_Methods;

// Box/unbox axiom for Tclass._module.DigitUnderscore__Names__Functions__and__Methods
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()) } 
  $IsBox(bx, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, 
        Tclass._module.DigitUnderscore__Names__Functions__and__Methods()));

// consequence axiom for _module.DigitUnderscore__Names__Functions__and__Methods._70
axiom 8 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._70(this) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(this)
         || (8 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()))
       ==> true);

function _module.DigitUnderscore__Names__Functions__and__Methods._70#requires(ref) : bool;

// #requires axiom for _module.DigitUnderscore__Names__Functions__and__Methods._70
axiom (forall this: ref :: 
  { _module.DigitUnderscore__Names__Functions__and__Methods._70#requires(this) } 
  this != null
       && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._70#requires(this)
       == true);

// definition axiom for _module.DigitUnderscore__Names__Functions__and__Methods._70 (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._70(this) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(this)
         || (8 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()))
       ==> _module.DigitUnderscore__Names__Functions__and__Methods._70(this) == LitInt(80));

// definition axiom for _module.DigitUnderscore__Names__Functions__and__Methods._70 for all literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    {:weight 3} { _module.DigitUnderscore__Names__Functions__and__Methods._70(Lit(this)) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(Lit(this))
         || (8 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()))
       ==> _module.DigitUnderscore__Names__Functions__and__Methods._70(Lit(this))
         == LitInt(80));

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._70(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction this} CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._120(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction this} Call$$_module.DigitUnderscore__Names__Functions__and__Methods._120(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(this);
  ensures LitInt(_module.DigitUnderscore__Names__Functions__and__Methods._70(this))
     == LitInt(80);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this} Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._120(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(this);
  ensures LitInt(_module.DigitUnderscore__Names__Functions__and__Methods._70(this))
     == LitInt(80);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction this} Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._120(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: 120, Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._120
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(338,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref :: 
      $Is($ih#this0#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
           && Lit(true)
           && false
         ==> LitInt(_module.DigitUnderscore__Names__Functions__and__Methods._70(this))
           == LitInt(80));
    $_reverifyPost := false;
}



function {:inline} _module.DigitUnderscore__Names__Functions__and__Methods._90(this: ref) : HandleType
{
  Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
        Handle0((lambda $l#0#heap#0: Heap :: $Box(LitInt(92))), 
          (lambda $l#0#heap#0: Heap :: true), 
          (lambda $l#0#heap#0: Heap :: SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
      $LS($LZ)))
}

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._90(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap;



// DigitUnderscore_Names_Functions_and_Methods.90: Type axiom
axiom 10 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._90($o) } 
    $Is(_module.DigitUnderscore__Names__Functions__and__Methods._90($o), 
      Tclass._System.___hTotalFunc0(TInt)));

// DigitUnderscore_Names_Functions_and_Methods.90: Allocation axiom
axiom 10 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._90($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.DigitUnderscore__Names__Functions__and__Methods._90($o), 
        Tclass._System.___hTotalFunc0(TInt), 
        $h));

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._567(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    y#0: int);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DigitUnderscore__Names__Functions__and__Methods._567(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._567(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._567(this: ref, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: HandleType
     where $Is(m#0, Tclass._System.___hTotalFunc0(TInt))
       && $IsAlloc(m#0, Tclass._System.___hTotalFunc0(TInt), $Heap);
  var k#0: int;
  var g#0_0: int;
  var y##0_0: int;

    // AddMethodImpl: 567, Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._567
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(342,21): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(343,11)
    assume true;
    assume true;
    m#0 := _module.DigitUnderscore__Names__Functions__and__Methods._90(this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(343,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(344,11)
    assume true;
    assume true;
    k#0 := $Unbox(Apply0(TInt, $Heap, _module.DigitUnderscore__Names__Functions__and__Methods._90(this))): int;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(344,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(345,5)
    assume true;
    assert k#0 == LitInt(92);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(346,5)
    assume true;
    if (0 < y#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(347,19)
        assume true;
        assume _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(this);
        assume _module.DigitUnderscore__Names__Functions__and__Methods._70#canCall(this);
        g#0_0 := LitInt(_module.DigitUnderscore__Names__Functions__and__Methods._70(this));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(347,30)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(348,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##0_0 := y#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= y#0 || y##0_0 == y#0;
        assert y##0_0 < y#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.DigitUnderscore__Names__Functions__and__Methods._567(this, y##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(348,19)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(349,7)
        assume true;
        assert g#0_0 == LitInt(80);
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._20_0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    x#0: int);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DigitUnderscore__Names__Functions__and__Methods._20_0(x#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._20_0(x#0: int)
   returns (this: ref
       where this != null
         && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()), 
    $_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function _module.DigitUnderscore__Names__Functions__and__Methods._88() : bool;

implementation Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._20_0(x#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var u#0: bool;

    // AddMethodImpl: 20_0, Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._20_0
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(354,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(354,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(355,11)
    assume true;
    assume true;
    u#0 := _module.DigitUnderscore__Names__Functions__and__Methods._88();
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(355,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(356,5)
    assume true;
    assert u#0 == _module.DigitUnderscore__Names__Functions__and__Methods._88();
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(354,3)
    assume !read($Heap, this, alloc);
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(354,3)
}



// DigitUnderscore_Names_Functions_and_Methods.88: Type axiom
axiom 12 < $FunctionContextHeight
   ==> $Is(_module.DigitUnderscore__Names__Functions__and__Methods._88(), TBool);

// DigitUnderscore_Names_Functions_and_Methods.88: Allocation axiom
axiom 12 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.DigitUnderscore__Names__Functions__and__Methods._88(), TBool, $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.DigitUnderscore__Names__Functions__and__Methods._88(), TBool, $h));

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._498(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DigitUnderscore__Names__Functions__and__Methods._498(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._498(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._498(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p#0: ref
     where $Is(p#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
       && $IsAlloc(p#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap);
  var $nw: ref;
  var x##0: int;
  var y##0: int;

    // AddMethodImpl: 498, Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._498
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(361,15): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(362,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(362,62)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(200);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.DigitUnderscore__Names__Functions__and__Methods._20_0(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(362,70)"} true;
    p#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(362,70)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(363,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert p#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := LitInt(100);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.DigitUnderscore__Names__Functions__and__Methods._567(p#0, y##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(363,14)"} true;
}



// function declaration for _module.DigitUnderscore_Names_Functions_and_Methods.500
function _module.DigitUnderscore__Names__Functions__and__Methods._500($ly: LayerType, this: ref, y#0: int) : bool;

function _module.DigitUnderscore__Names__Functions__and__Methods._500#canCall(this: ref, y#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: ref, y#0: int :: 
  { _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0) } 
  _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0)
     == _module.DigitUnderscore__Names__Functions__and__Methods._500($ly, this, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: ref, y#0: int :: 
  { _module.DigitUnderscore__Names__Functions__and__Methods._500(AsFuelBottom($ly), this, y#0) } 
  _module.DigitUnderscore__Names__Functions__and__Methods._500($ly, this, y#0)
     == _module.DigitUnderscore__Names__Functions__and__Methods._500($LZ, this, y#0));

// consequence axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500
axiom 0 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref, y#0: int :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500($ly, this, y#0) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._500#canCall(this, y#0)
         || (0 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()))
       ==> true);

function _module.DigitUnderscore__Names__Functions__and__Methods._500#requires(LayerType, ref, int) : bool;

// #requires axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, y#0: int :: 
  { _module.DigitUnderscore__Names__Functions__and__Methods._500#requires($ly, this, y#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
       && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap)
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#requires($ly, this, y#0)
       == true);

// definition axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500 (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, y#0: int :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0), $IsGoodHeap($Heap) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._500#canCall(this, y#0)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
           && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap))
       ==> (y#0 != LitInt(0)
           ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#canCall(this, y#0 - 1))
         && _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0)
           == (y#0 == LitInt(0)
             || _module.DigitUnderscore__Names__Functions__and__Methods._500($ly, this, y#0 - 1)));

// 1st prefix predicate axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500#
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref, y#0: int :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0) } 
    this != null
         && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0)
       ==> (exists _k#0: Box :: 
        { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0) } 
        _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0)));

// 2nd prefix predicate axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref, y#0: int :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0) } 
    this != null
         && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && (exists _k#0: Box :: 
          { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0) } 
          _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0))
       ==> _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($ly), this, y#0));

// 3rd prefix predicate axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref, y#0: int, _k#0: Box :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k#0, y#0) } 
    this != null
         && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && _k#0 == ORD#FromNat(0)
       ==> !_module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k#0, y#0));

// targeted prefix predicate monotonicity axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref, y#0: int, _k#0: Box, _m: Box, _limit: Box :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k#0, y#0), ORD#LessThanLimit(_k#0, _limit), ORD#LessThanLimit(_m, _limit) } 
    ORD#Less(_k#0, _m)
       ==> 
      _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k#0, y#0)
       ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _m, y#0));

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._500(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    y#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._500(this: ref, y#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##y#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function 500
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(366,18): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (y#0 != LitInt(0))
        {
            ##y#0 := y#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0, TInt, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.DigitUnderscore__Names__Functions__and__Methods._500#canCall(this, y#0 - 1);
        }

        assume _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($LZ), this, y#0)
           == (y#0 == LitInt(0)
             || _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($LZ), this, y#0 - 1));
        assume y#0 != LitInt(0)
           ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#canCall(this, y#0 - 1);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.DigitUnderscore__Names__Functions__and__Methods._500($LS($LZ), this, y#0), 
          TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module.DigitUnderscore_Names_Functions_and_Methods.500#
function _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly: LayerType, this: ref, _k#0: Box, y#0: int) : bool;

function _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this: ref, _k#0: Box, y#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: ref, _k#0: Box, y#0: int :: 
  { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0) } 
  _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0)
     == _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: ref, _k#0: Box, y#0: int :: 
  { _module.DigitUnderscore__Names__Functions__and__Methods._500#(AsFuelBottom($ly), this, _k#0, y#0) } 
  _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k#0, y#0)
     == _module.DigitUnderscore__Names__Functions__and__Methods._500#($LZ, this, _k#0, y#0));

// consequence axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500#
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref, _k#0: Box, y#0: int :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k#0, y#0) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k#0, y#0)
         || (1 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()))
       ==> true);

function _module.DigitUnderscore__Names__Functions__and__Methods._500##requires(LayerType, ref, Box, int) : bool;

// #requires axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500#
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, _k#0: Box, y#0: int :: 
  { _module.DigitUnderscore__Names__Functions__and__Methods._500##requires($ly, this, _k#0, y#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
       && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap)
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._500##requires($ly, this, _k#0, y#0)
       == true);

// definition axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500# (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, _k#0: Box, y#0: int :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0), $IsGoodHeap($Heap) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k#0, y#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
           && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          y#0 != LitInt(0)
           ==> _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
         && (
          (0 < ORD#Offset(_k#0)
           ==> y#0 == LitInt(0)
             || _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k'#0, y#0) } 
            ORD#LessThanLimit(_k'#0, _k#0)
               ==> _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k'#0, y#0)))
         && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k#0, y#0)
           == ((0 < ORD#Offset(_k#0)
               ==> y#0 == LitInt(0)
                 || _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#0: Box :: 
                { _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k'#0, y#0) } 
                ORD#LessThanLimit(_k'#0, _k#0)
                   && _module.DigitUnderscore__Names__Functions__and__Methods._500#($ly, this, _k'#0, y#0)))));

// definition axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500# for decreasing-related literals (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, _k#0: Box, y#0: int :: 
    {:weight 3} { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, Lit(_k#0), y#0), $IsGoodHeap($Heap) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, Lit(_k#0), y#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
           && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          y#0 != LitInt(0)
           ==> _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
         && (
          (0 < ORD#Offset(_k#0)
           ==> y#0 == LitInt(0)
             || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k'#1, y#0) } 
            ORD#LessThanLimit(_k'#1, _k#0)
               ==> _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k'#1, y#0)))
         && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, Lit(_k#0), y#0)
           == ((0 < ORD#Offset(_k#0)
               ==> y#0 == LitInt(0)
                 || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#1: Box :: 
                { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k'#1, y#0) } 
                ORD#LessThanLimit(_k'#1, _k#0)
                   && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k'#1, y#0)))));

// definition axiom for _module.DigitUnderscore__Names__Functions__and__Methods._500# for all literals (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, _k#0: Box, y#0: int :: 
    {:weight 3} { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), Lit(this), Lit(_k#0), LitInt(y#0)), $IsGoodHeap($Heap) } 
    _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(Lit(this), Lit(_k#0), LitInt(y#0))
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
           && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          y#0 != LitInt(0)
           ==> _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(Lit(this), ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
         && (
          (0 < ORD#Offset(_k#0)
           ==> y#0 == LitInt(0)
             || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), Lit(this), ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k'#2, y#0) } 
            ORD#LessThanLimit(_k'#2, _k#0)
               ==> _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k'#2, y#0)))
         && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), Lit(this), Lit(_k#0), LitInt(y#0))
           == ((0 < ORD#Offset(_k#0)
               ==> y#0 == LitInt(0)
                 || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), Lit(this), ORD#Minus(_k#0, ORD#FromNat(1)), y#0 - 1))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#2: Box :: 
                { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k'#2, y#0) } 
                ORD#LessThanLimit(_k'#2, _k#0)
                   && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($ly), this, _k'#2, y#0)))));

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods._5_0_0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    y#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DigitUnderscore__Names__Functions__and__Methods._5_0_0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    y#0: int);
  // user-defined preconditions
  requires _module.DigitUnderscore__Names__Functions__and__Methods._500#canCall(this, y#0)
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($LZ), this, y#0)
       || 
      y#0 == LitInt(0)
       || _module.DigitUnderscore__Names__Functions__and__Methods._500($LS($LS($LZ)), this, y#0 - 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= y#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this, _k#0, y#1} CoCall$$_module.DigitUnderscore__Names__Functions__and__Methods._5_0_0#(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    _k#0: Box, 
    y#1: int);
  // user-defined preconditions
  requires _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k#0, y#1)
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k#0, y#1)
       || (0 < ORD#Offset(_k#0)
         ==> y#1 == LitInt(0)
           || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LS($LZ)), this, ORD#Minus(_k#0, ORD#FromNat(1)), y#1 - 1));
  requires _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k#0, y#1)
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k#0, y#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (exists _k'#0: Box :: 
          { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#0, y#1) } 
          ORD#LessThanLimit(_k'#0, _k#0)
             && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#0, y#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= y#1;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this, _k#0, y#1} Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._5_0_0#(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    _k#0: Box, 
    y#1: int)
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, _k#0, y#1)
     && 
    _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k#0, y#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> y#1 == LitInt(0)
         || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, ORD#Minus(_k#0, ORD#FromNat(1)), y#1 - 1))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (exists _k'#1: Box :: 
        { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#1, y#1) } 
        ORD#LessThanLimit(_k'#1, _k#0)
           && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#1, y#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= y#1;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction this, _k#0, y#1} Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._5_0_0#(this: ref, _k#0: Box, y#1: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: 5_0_0#, Impl$$_module.DigitUnderscore__Names__Functions__and__Methods._5_0_0#
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(371,14): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, $ih#_k0#0: Box, $ih#y0#0: int :: 
      $Is($ih#this0#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
           && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), $ih#this0#0, $ih#_k0#0, $ih#y0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && 0 <= $ih#y0#0 && $ih#y0#0 < y#1))
         ==> LitInt(0) <= $ih#y0#0);
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(374,3)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(371,15)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, y#2: int :: 
          ORD#Less(_k'#2, _k#0)
               && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#2, y#2)
             ==> LitInt(0) <= y#2);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(371,14)"} true;
    }
}



procedure {:_induction this, k#0, y#0} CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods.Another(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    k#0: Box, 
    y#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction this, k#0, y#0} Call$$_module.DigitUnderscore__Names__Functions__and__Methods.Another(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    k#0: Box, 
    y#0: int);
  // user-defined preconditions
  requires _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, k#0, y#0)
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, k#0, y#0)
       || (0 < ORD#Offset(k#0)
         ==> y#0 == LitInt(0)
           || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LS($LZ)), this, ORD#Minus(k#0, ORD#FromNat(1)), y#0 - 1));
  requires _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, k#0, y#0)
     ==> _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, k#0, y#0)
       || (LitInt(0) == ORD#Offset(k#0)
         ==> (exists _k'#0: Box :: 
          { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#0, y#0) } 
          ORD#LessThanLimit(_k'#0, k#0)
             && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#0, y#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= y#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this, k#0, y#0} Impl$$_module.DigitUnderscore__Names__Functions__and__Methods.Another(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    k#0: Box, 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.DigitUnderscore__Names__Functions__and__Methods._500##canCall(this, k#0, y#0)
     && 
    _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, k#0, y#0)
     && 
    (0 < ORD#Offset(k#0)
       ==> y#0 == LitInt(0)
         || _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, ORD#Minus(k#0, ORD#FromNat(1)), y#0 - 1))
     && (LitInt(0) == ORD#Offset(k#0)
       ==> (exists _k'#1: Box :: 
        { _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#1, y#0) } 
        ORD#LessThanLimit(_k'#1, k#0)
           && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), this, _k'#1, y#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= y#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction this, k#0, y#0} Impl$$_module.DigitUnderscore__Names__Functions__and__Methods.Another(this: ref, k#0: Box, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: Box;
  var y##0: int;

    // AddMethodImpl: Another, Impl$$_module.DigitUnderscore__Names__Functions__and__Methods.Another
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(379,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, $ih#k0#0: Box, $ih#y0#0: int :: 
      $Is($ih#this0#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
           && _module.DigitUnderscore__Names__Functions__and__Methods._500#($LS($LZ), $ih#this0#0, $ih#k0#0, $ih#y0#0)
           && (ORD#Less($ih#k0#0, k#0)
             || ($ih#k0#0 == k#0 && 0 <= $ih#y0#0 && $ih#y0#0 < y#0))
         ==> LitInt(0) <= $ih#y0#0);
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(380,19)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    _k##0 := k#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := y#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call CoCall$$_module.DigitUnderscore__Names__Functions__and__Methods._5_0_0#(this, _k##0, y##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(380,21)"} true;
}



function {:inline} _module.DigitUnderscore__Names__Functions__and__Methods.x_k(this: ref) : real
{
  LitReal(3e0)
}

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods.x_k(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap;



// DigitUnderscore_Names_Functions_and_Methods.x': Type axiom
axiom 16 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods.x_k($o) } 
    $Is(_module.DigitUnderscore__Names__Functions__and__Methods.x_k($o), TReal));

// DigitUnderscore_Names_Functions_and_Methods.x': Allocation axiom
axiom 16 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.DigitUnderscore__Names__Functions__and__Methods.x_k($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.DigitUnderscore__Names__Functions__and__Methods.x_k($o), TReal, $h));

procedure CheckWellformed$$_module.DigitUnderscore__Names__Functions__and__Methods.Regression(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    u#0: real)
   returns (v#0: real);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DigitUnderscore__Names__Functions__and__Methods.Regression(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    u#0: real)
   returns (v#0: real);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.DigitUnderscore__Names__Functions__and__Methods.Regression(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
         && $IsAlloc(this, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $Heap), 
    u#0: real)
   returns (v#0: real, $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.DigitUnderscore_Names_Functions_and_Methods: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods()) } 
  $Is(c#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods())
     <==> $Is(c#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?())
       && c#0 != null);

// _module.DigitUnderscore_Names_Functions_and_Methods: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $h) } 
  $IsAlloc(c#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods(), $h)
     <==> $IsAlloc(c#0, Tclass._module.DigitUnderscore__Names__Functions__and__Methods?(), $h));

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

procedure CheckWellformed$$_module.__default.NotMain();
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.NotMain();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.NotMain() returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.NotMain() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: NotMain, Impl$$_module.__default.NotMain
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(126,17): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(127,8)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$A.__default.run();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(127,9)"} true;
}



procedure CheckWellformed$$_module.__default.Caller();
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Caller();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Caller() returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass.M.public() : Ty;

const unique Tagclass.M.public: TyTag;

// Tclass.M.public Tag
axiom Tag(Tclass.M.public()) == Tagclass.M.public
   && TagFamily(Tclass.M.public()) == tytagFamily$public;

// Box/unbox axiom for Tclass.M.public
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M.public()) } 
  $IsBox(bx, Tclass.M.public())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M.public()));

axiom FDim(M.public.private) == 0
   && FieldOfDecl(class.M.public?, field$private) == M.public.private
   && !$IsGhostField(M.public.private);

function M.public.namespace(this: ref) : int;

function M.public.fallthrough(this: ref) : int;

function M.public.try(this: ref) : int;

implementation Impl$$_module.__default.Caller() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p#0: ref
     where $Is(p#0, Tclass.M.public()) && $IsAlloc(p#0, Tclass.M.public(), $Heap);
  var $nw: ref;
  var x#0: int;

    // AddMethodImpl: Caller, Impl$$_module.__default.Caller
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(164,16): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(165,9)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(165,12)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$M.public.__ctor();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(165,25)"} true;
    p#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(165,25)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(166,9)
    assume true;
    assert p#0 != null;
    assert p#0 != null;
    assert p#0 != null;
    assert p#0 != null;
    assume true;
    x#0 := read($Heap, p#0, M.public.private)
       + M.public.namespace(p#0)
       + M.public.fallthrough(p#0)
       + M.public.try(p#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(166,58)"} true;
}



procedure CheckWellformed$$_module.__default.DigitsIdents(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tuple(TInt, Tclass._module.Tuple(TInt, TBool)))
         && $IsAlloc(t#0, Tclass._module.Tuple(TInt, Tclass._module.Tuple(TInt, TBool)), $Heap)
         && $IsA#_module.Tuple(t#0));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.DigitsIdents(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tuple(TInt, Tclass._module.Tuple(TInt, TBool)))
         && $IsAlloc(t#0, Tclass._module.Tuple(TInt, Tclass._module.Tuple(TInt, TBool)), $Heap)
         && $IsA#_module.Tuple(t#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.DigitsIdents(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tuple(TInt, Tclass._module.Tuple(TInt, TBool)))
         && $IsAlloc(t#0, Tclass._module.Tuple(TInt, Tclass._module.Tuple(TInt, TBool)), $Heap)
         && $IsA#_module.Tuple(t#0))
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.m__nobody() returns (y#0: int);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m__nobody() returns (y#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures y#0 > 5;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure CheckWellformed$$_module.__default.l__nobody() returns (y#0: int);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.l__nobody() returns (y#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures y#0 > 5;
  // frame condition
  free ensures old($Heap) == $Heap;



// function declaration for _module._default.f_nobody
function _module.__default.f__nobody() : int;

function _module.__default.f__nobody#canCall() : bool;

// consequence axiom for _module.__default.f__nobody
axiom 20 <= $FunctionContextHeight
   ==> 
  _module.__default.f__nobody#canCall() || 20 != $FunctionContextHeight
   ==> _module.__default.f__nobody() > 5;

function _module.__default.f__nobody#requires() : bool;

// #requires axiom for _module.__default.f__nobody
axiom _module.__default.f__nobody#requires() == true;

procedure CheckWellformed$$_module.__default.f__nobody();
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.f__nobody() > 5;



implementation CheckWellformed$$_module.__default.f__nobody()
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function f_nobody
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(196,18): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    if (*)
    {
        assert true;
        assume true;
        assume _module.__default.f__nobody() > 5;
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.hidden
function _module.__default.hidden($ly: LayerType) : int;

function _module.__default.hidden#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.hidden($LS($ly)) } 
  _module.__default.hidden($LS($ly)) == _module.__default.hidden($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.hidden(AsFuelBottom($ly)) } 
  _module.__default.hidden($ly) == _module.__default.hidden($LZ));

// consequence axiom for _module.__default.hidden
axiom 22 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.hidden($ly) } 
    _module.__default.hidden#canCall() || 22 != $FunctionContextHeight ==> true);

function _module.__default.hidden#requires(LayerType) : bool;

// #requires axiom for _module.__default.hidden
axiom (forall $ly: LayerType :: 
  { _module.__default.hidden#requires($ly) } 
  _module.__default.hidden#requires($ly) == true);

// definition axiom for _module.__default.hidden (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.hidden($LS($ly)) } 
    _module.__default.hidden#canCall() || 22 != $FunctionContextHeight
       ==> _module.__default.hidden($LS($ly)) == LitInt(7));

// definition axiom for _module.__default.hidden for all literals (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    {:weight 3} { _module.__default.hidden($LS($ly)) } 
    _module.__default.hidden#canCall() || 22 != $FunctionContextHeight
       ==> _module.__default.hidden($LS($ly)) == LitInt(7));

procedure {:opaque} CheckWellformed$$_module.__default.hidden();
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.hidden__test();
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.hidden__test();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.hidden__test() returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.hidden__test() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: hidden_test, Impl$$_module.__default.hidden__test
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(206,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(207,3)
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(207,16)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__hidden();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(207,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(208,3)
    assume _module.__default.hidden#canCall();
    assume _module.__default.hidden#canCall();
    assert {:subsumption 0} _module.__default.hidden(StartFuelAssert__module._default.hidden) == LitInt(7);
    assume _module.__default.hidden(StartFuel__module._default.hidden) == LitInt(7);
}



procedure CheckWellformed$$_module.__default._default_Main();
  free requires 28 == $FunctionContextHeight;
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
  free requires 28 == $FunctionContextHeight;
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
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(268,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(269,23)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$CoRecursion.__default.TestMain();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(269,24)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(270,25)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$EqualityTests.__default.TestMain();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(270,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(271,30)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$TypeInstantiations.__default.TestMain();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(271,31)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(272,50)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$TailRecursionWhereTypeParametersChange.__default.TestMain();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(272,51)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(273,19)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$GeneralMaps.__default.Test();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(273,20)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(274,21)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$Cardinalities.__default.Test();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(274,22)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(275,15)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$AltLoop.__default.Test();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(275,16)"} true;
}



procedure CheckWellformed$$_module.__default.N();
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.N();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.N() returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.N() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: int where LitInt(0) <= z#0;
  var z#1: int;

    // AddMethodImpl: N, Impl$$_module.__default.N
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.hidden)
       == StartFuel__module._default.hidden;
    assume AsFuelBottom(StartFuelAssert__module._default.hidden)
       == StartFuelAssert__module._default.hidden;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(327,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(328,14)
    havoc z#1;
    if (LitInt(0) <= z#1)
    {
        assume true;
    }

    assert true;
    havoc z#0;
    assume true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(328,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Compilation.dfy(329,3)
    assume true;
    assert LitInt(0) <= z#0;
}



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$_module.__default.reveal__hidden();
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel__module._default.hidden0: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$_module.__default.reveal__hidden();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel__module._default.hidden == $LS(MoreFuel__module._default.hidden0);
  free ensures StartFuelAssert__module._default.hidden
     == $LS($LS(MoreFuel__module._default.hidden0));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel__module._default.hidden0)
     == MoreFuel__module._default.hidden0;



// Constructor function declaration
function #OnceBuggy.MyDt.Nil() : DatatypeType;

const unique ##OnceBuggy.MyDt.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#OnceBuggy.MyDt.Nil()) == ##OnceBuggy.MyDt.Nil;

function OnceBuggy.MyDt.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { OnceBuggy.MyDt.Nil_q(d) } 
  OnceBuggy.MyDt.Nil_q(d) <==> DatatypeCtorId(d) == ##OnceBuggy.MyDt.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { OnceBuggy.MyDt.Nil_q(d) } 
  OnceBuggy.MyDt.Nil_q(d) ==> d == #OnceBuggy.MyDt.Nil());

function Tclass.OnceBuggy.MyDt(Ty) : Ty;

const unique Tagclass.OnceBuggy.MyDt: TyTag;

// Tclass.OnceBuggy.MyDt Tag
axiom (forall OnceBuggy.MyDt$T: Ty :: 
  { Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T) } 
  Tag(Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)) == Tagclass.OnceBuggy.MyDt
     && TagFamily(Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)) == tytagFamily$MyDt);

// Tclass.OnceBuggy.MyDt injectivity 0
axiom (forall OnceBuggy.MyDt$T: Ty :: 
  { Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T) } 
  Tclass.OnceBuggy.MyDt_0(Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T))
     == OnceBuggy.MyDt$T);

function Tclass.OnceBuggy.MyDt_0(Ty) : Ty;

// Box/unbox axiom for Tclass.OnceBuggy.MyDt
axiom (forall OnceBuggy.MyDt$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)) } 
  $IsBox(bx, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)));

// Constructor $Is
axiom (forall OnceBuggy.MyDt$T: Ty :: 
  { $Is(#OnceBuggy.MyDt.Nil(), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)) } 
  $Is(#OnceBuggy.MyDt.Nil(), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)));

// Constructor $IsAlloc
axiom (forall OnceBuggy.MyDt$T: Ty, $h: Heap :: 
  { $IsAlloc(#OnceBuggy.MyDt.Nil(), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#OnceBuggy.MyDt.Nil(), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), $h));

// Constructor literal
axiom #OnceBuggy.MyDt.Nil() == Lit(#OnceBuggy.MyDt.Nil());

// Constructor function declaration
function #OnceBuggy.MyDt.Cons(Box, DatatypeType) : DatatypeType;

const unique ##OnceBuggy.MyDt.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: DatatypeType :: 
  { #OnceBuggy.MyDt.Cons(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#OnceBuggy.MyDt.Cons(a#5#0#0, a#5#1#0)) == ##OnceBuggy.MyDt.Cons);

function OnceBuggy.MyDt.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { OnceBuggy.MyDt.Cons_q(d) } 
  OnceBuggy.MyDt.Cons_q(d) <==> DatatypeCtorId(d) == ##OnceBuggy.MyDt.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { OnceBuggy.MyDt.Cons_q(d) } 
  OnceBuggy.MyDt.Cons_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: DatatypeType :: 
      d == #OnceBuggy.MyDt.Cons(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall OnceBuggy.MyDt$T: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType :: 
  { $Is(#OnceBuggy.MyDt.Cons(a#7#0#0, a#7#1#0), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)) } 
  $Is(#OnceBuggy.MyDt.Cons(a#7#0#0, a#7#1#0), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T))
     <==> $IsBox(a#7#0#0, OnceBuggy.MyDt$T)
       && $Is(a#7#1#0, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)));

// Constructor $IsAlloc
axiom (forall OnceBuggy.MyDt$T: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#OnceBuggy.MyDt.Cons(a#8#0#0, a#8#1#0), 
      Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#OnceBuggy.MyDt.Cons(a#8#0#0, a#8#1#0), 
        Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), 
        $h)
       <==> $IsAllocBox(a#8#0#0, OnceBuggy.MyDt$T, $h)
         && $IsAlloc(a#8#1#0, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, OnceBuggy.MyDt$T: Ty, $h: Heap :: 
  { $IsAllocBox(OnceBuggy.MyDt._h0(d), OnceBuggy.MyDt$T, $h) } 
  $IsGoodHeap($h)
       && 
      OnceBuggy.MyDt.Cons_q(d)
       && $IsAlloc(d, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), $h)
     ==> $IsAllocBox(OnceBuggy.MyDt._h0(d), OnceBuggy.MyDt$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, OnceBuggy.MyDt$T: Ty, $h: Heap :: 
  { $IsAlloc(OnceBuggy.MyDt._h1(d), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), $h) } 
  $IsGoodHeap($h)
       && 
      OnceBuggy.MyDt.Cons_q(d)
       && $IsAlloc(d, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), $h)
     ==> $IsAlloc(OnceBuggy.MyDt._h1(d), Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #OnceBuggy.MyDt.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #OnceBuggy.MyDt.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#OnceBuggy.MyDt.Cons(a#9#0#0, a#9#1#0)));

function OnceBuggy.MyDt._h0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #OnceBuggy.MyDt.Cons(a#10#0#0, a#10#1#0) } 
  OnceBuggy.MyDt._h0(#OnceBuggy.MyDt.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #OnceBuggy.MyDt.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#OnceBuggy.MyDt.Cons(a#11#0#0, a#11#1#0)));

function OnceBuggy.MyDt._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #OnceBuggy.MyDt.Cons(a#12#0#0, a#12#1#0) } 
  OnceBuggy.MyDt._h1(#OnceBuggy.MyDt.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: DatatypeType :: 
  { #OnceBuggy.MyDt.Cons(a#13#0#0, a#13#1#0) } 
  DtRank(a#13#1#0) < DtRank(#OnceBuggy.MyDt.Cons(a#13#0#0, a#13#1#0)));

// Depth-one case-split function
function $IsA#OnceBuggy.MyDt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#OnceBuggy.MyDt(d) } 
  $IsA#OnceBuggy.MyDt(d) ==> OnceBuggy.MyDt.Nil_q(d) || OnceBuggy.MyDt.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall OnceBuggy.MyDt$T: Ty, d: DatatypeType :: 
  { OnceBuggy.MyDt.Cons_q(d), $Is(d, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)) } 
    { OnceBuggy.MyDt.Nil_q(d), $Is(d, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T)) } 
  $Is(d, Tclass.OnceBuggy.MyDt(OnceBuggy.MyDt$T))
     ==> OnceBuggy.MyDt.Nil_q(d) || OnceBuggy.MyDt.Cons_q(d));

// Datatype extensional equality declaration
function OnceBuggy.MyDt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #OnceBuggy.MyDt.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { OnceBuggy.MyDt#Equal(a, b), OnceBuggy.MyDt.Nil_q(a) } 
    { OnceBuggy.MyDt#Equal(a, b), OnceBuggy.MyDt.Nil_q(b) } 
  OnceBuggy.MyDt.Nil_q(a) && OnceBuggy.MyDt.Nil_q(b)
     ==> (OnceBuggy.MyDt#Equal(a, b) <==> true));

// Datatype extensional equality definition: #OnceBuggy.MyDt.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { OnceBuggy.MyDt#Equal(a, b), OnceBuggy.MyDt.Cons_q(a) } 
    { OnceBuggy.MyDt#Equal(a, b), OnceBuggy.MyDt.Cons_q(b) } 
  OnceBuggy.MyDt.Cons_q(a) && OnceBuggy.MyDt.Cons_q(b)
     ==> (OnceBuggy.MyDt#Equal(a, b)
       <==> OnceBuggy.MyDt._h0(a) == OnceBuggy.MyDt._h0(b)
         && OnceBuggy.MyDt#Equal(OnceBuggy.MyDt._h1(a), OnceBuggy.MyDt._h1(b))));

// Datatype extensionality axiom: OnceBuggy.MyDt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { OnceBuggy.MyDt#Equal(a, b) } 
  OnceBuggy.MyDt#Equal(a, b) <==> a == b);

const unique class.OnceBuggy.MyDt: ClassName;

const unique class.OnceBuggy.__default: ClassName;

function Tclass.OnceBuggy.__default() : Ty;

const unique Tagclass.OnceBuggy.__default: TyTag;

// Tclass.OnceBuggy.__default Tag
axiom Tag(Tclass.OnceBuggy.__default()) == Tagclass.OnceBuggy.__default
   && TagFamily(Tclass.OnceBuggy.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.OnceBuggy.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.OnceBuggy.__default()) } 
  $IsBox(bx, Tclass.OnceBuggy.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.OnceBuggy.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.OnceBuggy.__default()) } 
  $Is($o, Tclass.OnceBuggy.__default())
     <==> $o == null || dtype($o) == Tclass.OnceBuggy.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.OnceBuggy.__default(), $h) } 
  $IsAlloc($o, Tclass.OnceBuggy.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// Constructor function declaration
function #CoRecursion.Stream.More(Box, DatatypeType) : DatatypeType;

const unique ##CoRecursion.Stream.More: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: DatatypeType :: 
  { #CoRecursion.Stream.More(a#14#0#0, a#14#1#0) } 
  DatatypeCtorId(#CoRecursion.Stream.More(a#14#0#0, a#14#1#0))
     == ##CoRecursion.Stream.More);

function CoRecursion.Stream.More_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { CoRecursion.Stream.More_q(d) } 
  CoRecursion.Stream.More_q(d) <==> DatatypeCtorId(d) == ##CoRecursion.Stream.More);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { CoRecursion.Stream.More_q(d) } 
  CoRecursion.Stream.More_q(d)
     ==> (exists a#15#0#0: Box, a#15#1#0: DatatypeType :: 
      d == #CoRecursion.Stream.More(a#15#0#0, a#15#1#0)));

function Tclass.CoRecursion.Stream(Ty) : Ty;

const unique Tagclass.CoRecursion.Stream: TyTag;

// Tclass.CoRecursion.Stream Tag
axiom (forall CoRecursion.Stream$T: Ty :: 
  { Tclass.CoRecursion.Stream(CoRecursion.Stream$T) } 
  Tag(Tclass.CoRecursion.Stream(CoRecursion.Stream$T))
       == Tagclass.CoRecursion.Stream
     && TagFamily(Tclass.CoRecursion.Stream(CoRecursion.Stream$T)) == tytagFamily$Stream);

// Tclass.CoRecursion.Stream injectivity 0
axiom (forall CoRecursion.Stream$T: Ty :: 
  { Tclass.CoRecursion.Stream(CoRecursion.Stream$T) } 
  Tclass.CoRecursion.Stream_0(Tclass.CoRecursion.Stream(CoRecursion.Stream$T))
     == CoRecursion.Stream$T);

function Tclass.CoRecursion.Stream_0(Ty) : Ty;

// Box/unbox axiom for Tclass.CoRecursion.Stream
axiom (forall CoRecursion.Stream$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.CoRecursion.Stream(CoRecursion.Stream$T)) } 
  $IsBox(bx, Tclass.CoRecursion.Stream(CoRecursion.Stream$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.CoRecursion.Stream(CoRecursion.Stream$T)));

// Constructor $Is
axiom (forall CoRecursion.Stream$T: Ty, a#16#0#0: Box, a#16#1#0: DatatypeType :: 
  { $Is(#CoRecursion.Stream.More(a#16#0#0, a#16#1#0), 
      Tclass.CoRecursion.Stream(CoRecursion.Stream$T)) } 
  $Is(#CoRecursion.Stream.More(a#16#0#0, a#16#1#0), 
      Tclass.CoRecursion.Stream(CoRecursion.Stream$T))
     <==> $IsBox(a#16#0#0, CoRecursion.Stream$T)
       && $Is(a#16#1#0, Tclass.CoRecursion.Stream(CoRecursion.Stream$T)));

// Constructor $IsAlloc
axiom (forall CoRecursion.Stream$T: Ty, a#17#0#0: Box, a#17#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#CoRecursion.Stream.More(a#17#0#0, a#17#1#0), 
      Tclass.CoRecursion.Stream(CoRecursion.Stream$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#CoRecursion.Stream.More(a#17#0#0, a#17#1#0), 
        Tclass.CoRecursion.Stream(CoRecursion.Stream$T), 
        $h)
       <==> $IsAllocBox(a#17#0#0, CoRecursion.Stream$T, $h)
         && $IsAlloc(a#17#1#0, Tclass.CoRecursion.Stream(CoRecursion.Stream$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, CoRecursion.Stream$T: Ty, $h: Heap :: 
  { $IsAllocBox(CoRecursion.Stream.head(d), CoRecursion.Stream$T, $h) } 
  $IsGoodHeap($h)
       && 
      CoRecursion.Stream.More_q(d)
       && $IsAlloc(d, Tclass.CoRecursion.Stream(CoRecursion.Stream$T), $h)
     ==> $IsAllocBox(CoRecursion.Stream.head(d), CoRecursion.Stream$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, CoRecursion.Stream$T: Ty, $h: Heap :: 
  { $IsAlloc(CoRecursion.Stream.rest(d), Tclass.CoRecursion.Stream(CoRecursion.Stream$T), $h) } 
  $IsGoodHeap($h)
       && 
      CoRecursion.Stream.More_q(d)
       && $IsAlloc(d, Tclass.CoRecursion.Stream(CoRecursion.Stream$T), $h)
     ==> $IsAlloc(CoRecursion.Stream.rest(d), Tclass.CoRecursion.Stream(CoRecursion.Stream$T), $h));

function CoRecursion.Stream.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#18#0#0: Box, a#18#1#0: DatatypeType :: 
  { #CoRecursion.Stream.More(a#18#0#0, a#18#1#0) } 
  CoRecursion.Stream.head(#CoRecursion.Stream.More(a#18#0#0, a#18#1#0))
     == a#18#0#0);

function CoRecursion.Stream.rest(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: DatatypeType :: 
  { #CoRecursion.Stream.More(a#19#0#0, a#19#1#0) } 
  CoRecursion.Stream.rest(#CoRecursion.Stream.More(a#19#0#0, a#19#1#0))
     == a#19#1#0);

// Depth-one case-split function
function $IsA#CoRecursion.Stream(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#CoRecursion.Stream(d) } 
  $IsA#CoRecursion.Stream(d) ==> CoRecursion.Stream.More_q(d));

// Questionmark data type disjunctivity
axiom (forall CoRecursion.Stream$T: Ty, d: DatatypeType :: 
  { CoRecursion.Stream.More_q(d), $Is(d, Tclass.CoRecursion.Stream(CoRecursion.Stream$T)) } 
  $Is(d, Tclass.CoRecursion.Stream(CoRecursion.Stream$T))
     ==> CoRecursion.Stream.More_q(d));

function $Eq#CoRecursion.Stream(Ty, Ty, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1) } 
  $Is(d0, Tclass.CoRecursion.Stream(CoRecursion.Stream$T#l))
       && $Is(d1, Tclass.CoRecursion.Stream(CoRecursion.Stream$T#r))
     ==> ($Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1)
       <==> CoRecursion.Stream.More_q(d0)
         && CoRecursion.Stream.More_q(d1)
         && (CoRecursion.Stream.More_q(d0) && CoRecursion.Stream.More_q(d1)
           ==> CoRecursion.Stream.head(d0) == CoRecursion.Stream.head(d1)
             && $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, 
              CoRecursion.Stream$T#r, 
              ly, 
              CoRecursion.Stream.rest(d0), 
              CoRecursion.Stream.rest(d1)))));

// Unbump layer co-equality axiom
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1) } 
  $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1)
     <==> $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, ly, d0, d1));

// Equality for codatatypes
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1) } 
  $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1)
     <==> d0 == d1);

function $PrefixEq#CoRecursion.Stream(Ty, Ty, Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass.CoRecursion.Stream(CoRecursion.Stream$T#l))
       && $Is(d1, Tclass.CoRecursion.Stream(CoRecursion.Stream$T#r))
     ==> ($PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> CoRecursion.Stream.More_q(d0)
             && CoRecursion.Stream.More_q(d1)
             && (CoRecursion.Stream.More_q(d0) && CoRecursion.Stream.More_q(d1)
               ==> CoRecursion.Stream.head(d0) == CoRecursion.Stream.head(d1)
                 && $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, 
                  CoRecursion.Stream$T#r, 
                  ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  CoRecursion.Stream.rest(d0), 
                  CoRecursion.Stream.rest(d1))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k)
           ==> $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1)
       <==> $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1) } 
  $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1) } 
      $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k
         ==> $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, $LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType, 
    m: Box :: 
  { $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1), $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, m, $LS(ly), d0, d1) } 
  ORD#Less(k, m)
       && $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, m, $LS(ly), d0, d1)
     ==> $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall CoRecursion.Stream$T#l: Ty, 
    CoRecursion.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1) } 
  d0 == d1
     ==> $PrefixEq#CoRecursion.Stream(CoRecursion.Stream$T#l, CoRecursion.Stream$T#r, k, $LS(ly), d0, d1));

const unique class.CoRecursion.Stream: ClassName;

// Constructor function declaration
function #CoRecursion.List.Nil() : DatatypeType;

const unique ##CoRecursion.List.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#CoRecursion.List.Nil()) == ##CoRecursion.List.Nil;

function CoRecursion.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { CoRecursion.List.Nil_q(d) } 
  CoRecursion.List.Nil_q(d) <==> DatatypeCtorId(d) == ##CoRecursion.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { CoRecursion.List.Nil_q(d) } 
  CoRecursion.List.Nil_q(d) ==> d == #CoRecursion.List.Nil());

function Tclass.CoRecursion.List(Ty) : Ty;

const unique Tagclass.CoRecursion.List: TyTag;

// Tclass.CoRecursion.List Tag
axiom (forall CoRecursion.List$T: Ty :: 
  { Tclass.CoRecursion.List(CoRecursion.List$T) } 
  Tag(Tclass.CoRecursion.List(CoRecursion.List$T)) == Tagclass.CoRecursion.List
     && TagFamily(Tclass.CoRecursion.List(CoRecursion.List$T)) == tytagFamily$List);

// Tclass.CoRecursion.List injectivity 0
axiom (forall CoRecursion.List$T: Ty :: 
  { Tclass.CoRecursion.List(CoRecursion.List$T) } 
  Tclass.CoRecursion.List_0(Tclass.CoRecursion.List(CoRecursion.List$T))
     == CoRecursion.List$T);

function Tclass.CoRecursion.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass.CoRecursion.List
axiom (forall CoRecursion.List$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.CoRecursion.List(CoRecursion.List$T)) } 
  $IsBox(bx, Tclass.CoRecursion.List(CoRecursion.List$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.CoRecursion.List(CoRecursion.List$T)));

// Constructor $Is
axiom (forall CoRecursion.List$T: Ty :: 
  { $Is(#CoRecursion.List.Nil(), Tclass.CoRecursion.List(CoRecursion.List$T)) } 
  $Is(#CoRecursion.List.Nil(), Tclass.CoRecursion.List(CoRecursion.List$T)));

// Constructor $IsAlloc
axiom (forall CoRecursion.List$T: Ty, $h: Heap :: 
  { $IsAlloc(#CoRecursion.List.Nil(), Tclass.CoRecursion.List(CoRecursion.List$T), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#CoRecursion.List.Nil(), Tclass.CoRecursion.List(CoRecursion.List$T), $h));

// Constructor literal
axiom #CoRecursion.List.Nil() == Lit(#CoRecursion.List.Nil());

// Constructor function declaration
function #CoRecursion.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##CoRecursion.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#25#0#0: Box, a#25#1#0: DatatypeType :: 
  { #CoRecursion.List.Cons(a#25#0#0, a#25#1#0) } 
  DatatypeCtorId(#CoRecursion.List.Cons(a#25#0#0, a#25#1#0))
     == ##CoRecursion.List.Cons);

function CoRecursion.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { CoRecursion.List.Cons_q(d) } 
  CoRecursion.List.Cons_q(d) <==> DatatypeCtorId(d) == ##CoRecursion.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { CoRecursion.List.Cons_q(d) } 
  CoRecursion.List.Cons_q(d)
     ==> (exists a#26#0#0: Box, a#26#1#0: DatatypeType :: 
      d == #CoRecursion.List.Cons(a#26#0#0, a#26#1#0)));

// Constructor $Is
axiom (forall CoRecursion.List$T: Ty, a#27#0#0: Box, a#27#1#0: DatatypeType :: 
  { $Is(#CoRecursion.List.Cons(a#27#0#0, a#27#1#0), 
      Tclass.CoRecursion.List(CoRecursion.List$T)) } 
  $Is(#CoRecursion.List.Cons(a#27#0#0, a#27#1#0), 
      Tclass.CoRecursion.List(CoRecursion.List$T))
     <==> $IsBox(a#27#0#0, CoRecursion.List$T)
       && $Is(a#27#1#0, Tclass.CoRecursion.List(CoRecursion.List$T)));

// Constructor $IsAlloc
axiom (forall CoRecursion.List$T: Ty, a#28#0#0: Box, a#28#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#CoRecursion.List.Cons(a#28#0#0, a#28#1#0), 
      Tclass.CoRecursion.List(CoRecursion.List$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#CoRecursion.List.Cons(a#28#0#0, a#28#1#0), 
        Tclass.CoRecursion.List(CoRecursion.List$T), 
        $h)
       <==> $IsAllocBox(a#28#0#0, CoRecursion.List$T, $h)
         && $IsAlloc(a#28#1#0, Tclass.CoRecursion.List(CoRecursion.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, CoRecursion.List$T: Ty, $h: Heap :: 
  { $IsAllocBox(CoRecursion.List.car(d), CoRecursion.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      CoRecursion.List.Cons_q(d)
       && $IsAlloc(d, Tclass.CoRecursion.List(CoRecursion.List$T), $h)
     ==> $IsAllocBox(CoRecursion.List.car(d), CoRecursion.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, CoRecursion.List$T: Ty, $h: Heap :: 
  { $IsAlloc(CoRecursion.List.cdr(d), Tclass.CoRecursion.List(CoRecursion.List$T), $h) } 
  $IsGoodHeap($h)
       && 
      CoRecursion.List.Cons_q(d)
       && $IsAlloc(d, Tclass.CoRecursion.List(CoRecursion.List$T), $h)
     ==> $IsAlloc(CoRecursion.List.cdr(d), Tclass.CoRecursion.List(CoRecursion.List$T), $h));

// Constructor literal
axiom (forall a#29#0#0: Box, a#29#1#0: DatatypeType :: 
  { #CoRecursion.List.Cons(Lit(a#29#0#0), Lit(a#29#1#0)) } 
  #CoRecursion.List.Cons(Lit(a#29#0#0), Lit(a#29#1#0))
     == Lit(#CoRecursion.List.Cons(a#29#0#0, a#29#1#0)));

function CoRecursion.List.car(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#30#0#0: Box, a#30#1#0: DatatypeType :: 
  { #CoRecursion.List.Cons(a#30#0#0, a#30#1#0) } 
  CoRecursion.List.car(#CoRecursion.List.Cons(a#30#0#0, a#30#1#0)) == a#30#0#0);

// Inductive rank
axiom (forall a#31#0#0: Box, a#31#1#0: DatatypeType :: 
  { #CoRecursion.List.Cons(a#31#0#0, a#31#1#0) } 
  BoxRank(a#31#0#0) < DtRank(#CoRecursion.List.Cons(a#31#0#0, a#31#1#0)));

function CoRecursion.List.cdr(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#32#0#0: Box, a#32#1#0: DatatypeType :: 
  { #CoRecursion.List.Cons(a#32#0#0, a#32#1#0) } 
  CoRecursion.List.cdr(#CoRecursion.List.Cons(a#32#0#0, a#32#1#0)) == a#32#1#0);

// Inductive rank
axiom (forall a#33#0#0: Box, a#33#1#0: DatatypeType :: 
  { #CoRecursion.List.Cons(a#33#0#0, a#33#1#0) } 
  DtRank(a#33#1#0) < DtRank(#CoRecursion.List.Cons(a#33#0#0, a#33#1#0)));

// Depth-one case-split function
function $IsA#CoRecursion.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#CoRecursion.List(d) } 
  $IsA#CoRecursion.List(d)
     ==> CoRecursion.List.Nil_q(d) || CoRecursion.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall CoRecursion.List$T: Ty, d: DatatypeType :: 
  { CoRecursion.List.Cons_q(d), $Is(d, Tclass.CoRecursion.List(CoRecursion.List$T)) } 
    { CoRecursion.List.Nil_q(d), $Is(d, Tclass.CoRecursion.List(CoRecursion.List$T)) } 
  $Is(d, Tclass.CoRecursion.List(CoRecursion.List$T))
     ==> CoRecursion.List.Nil_q(d) || CoRecursion.List.Cons_q(d));

// Datatype extensional equality declaration
function CoRecursion.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #CoRecursion.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { CoRecursion.List#Equal(a, b), CoRecursion.List.Nil_q(a) } 
    { CoRecursion.List#Equal(a, b), CoRecursion.List.Nil_q(b) } 
  CoRecursion.List.Nil_q(a) && CoRecursion.List.Nil_q(b)
     ==> (CoRecursion.List#Equal(a, b) <==> true));

// Datatype extensional equality definition: #CoRecursion.List.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { CoRecursion.List#Equal(a, b), CoRecursion.List.Cons_q(a) } 
    { CoRecursion.List#Equal(a, b), CoRecursion.List.Cons_q(b) } 
  CoRecursion.List.Cons_q(a) && CoRecursion.List.Cons_q(b)
     ==> (CoRecursion.List#Equal(a, b)
       <==> CoRecursion.List.car(a) == CoRecursion.List.car(b)
         && CoRecursion.List#Equal(CoRecursion.List.cdr(a), CoRecursion.List.cdr(b))));

// Datatype extensionality axiom: CoRecursion.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { CoRecursion.List#Equal(a, b) } 
  CoRecursion.List#Equal(a, b) <==> a == b);

const unique class.CoRecursion.List: ClassName;

const unique class.CoRecursion.Cell?: ClassName;

function Tclass.CoRecursion.Cell?() : Ty;

const unique Tagclass.CoRecursion.Cell?: TyTag;

// Tclass.CoRecursion.Cell? Tag
axiom Tag(Tclass.CoRecursion.Cell?()) == Tagclass.CoRecursion.Cell?
   && TagFamily(Tclass.CoRecursion.Cell?()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.CoRecursion.Cell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.CoRecursion.Cell?()) } 
  $IsBox(bx, Tclass.CoRecursion.Cell?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.CoRecursion.Cell?()));

// Cell: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.CoRecursion.Cell?()) } 
  $Is($o, Tclass.CoRecursion.Cell?())
     <==> $o == null || dtype($o) == Tclass.CoRecursion.Cell?());

// Cell: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.CoRecursion.Cell?(), $h) } 
  $IsAlloc($o, Tclass.CoRecursion.Cell?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(CoRecursion.Cell.data) == 0
   && FieldOfDecl(class.CoRecursion.Cell?, field$data) == CoRecursion.Cell.data
   && !$IsGhostField(CoRecursion.Cell.data);

const CoRecursion.Cell.data: Field int;

// Cell.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, CoRecursion.Cell.data) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.CoRecursion.Cell?()
     ==> $Is(read($h, $o, CoRecursion.Cell.data), TInt));

// Cell.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, CoRecursion.Cell.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.CoRecursion.Cell?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, CoRecursion.Cell.data), TInt, $h));

function Tclass.CoRecursion.Cell() : Ty;

const unique Tagclass.CoRecursion.Cell: TyTag;

// Tclass.CoRecursion.Cell Tag
axiom Tag(Tclass.CoRecursion.Cell()) == Tagclass.CoRecursion.Cell
   && TagFamily(Tclass.CoRecursion.Cell()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.CoRecursion.Cell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.CoRecursion.Cell()) } 
  $IsBox(bx, Tclass.CoRecursion.Cell())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.CoRecursion.Cell()));

// CoRecursion.Cell: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.CoRecursion.Cell()) } 
  $Is(c#0, Tclass.CoRecursion.Cell())
     <==> $Is(c#0, Tclass.CoRecursion.Cell?()) && c#0 != null);

// CoRecursion.Cell: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.CoRecursion.Cell(), $h) } 
  $IsAlloc(c#0, Tclass.CoRecursion.Cell(), $h)
     <==> $IsAlloc(c#0, Tclass.CoRecursion.Cell?(), $h));

const unique class.CoRecursion.__default: ClassName;

function Tclass.CoRecursion.__default() : Ty;

const unique Tagclass.CoRecursion.__default: TyTag;

// Tclass.CoRecursion.__default Tag
axiom Tag(Tclass.CoRecursion.__default()) == Tagclass.CoRecursion.__default
   && TagFamily(Tclass.CoRecursion.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.CoRecursion.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.CoRecursion.__default()) } 
  $IsBox(bx, Tclass.CoRecursion.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.CoRecursion.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.CoRecursion.__default()) } 
  $Is($o, Tclass.CoRecursion.__default())
     <==> $o == null || dtype($o) == Tclass.CoRecursion.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.CoRecursion.__default(), $h) } 
  $IsAlloc($o, Tclass.CoRecursion.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for CoRecursion._default.AscendingChain
function CoRecursion.__default.AscendingChain($ly: LayerType, n#0: int) : DatatypeType;

function CoRecursion.__default.AscendingChain#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { CoRecursion.__default.AscendingChain($LS($ly), n#0) } 
  CoRecursion.__default.AscendingChain($LS($ly), n#0)
     == CoRecursion.__default.AscendingChain($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { CoRecursion.__default.AscendingChain(AsFuelBottom($ly), n#0) } 
  CoRecursion.__default.AscendingChain($ly, n#0)
     == CoRecursion.__default.AscendingChain($LZ, n#0));

// consequence axiom for CoRecursion.__default.AscendingChain
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    { CoRecursion.__default.AscendingChain($ly, n#0) } 
    true
       ==> $Is(CoRecursion.__default.AscendingChain($ly, n#0), Tclass.CoRecursion.Stream(TInt)));

function CoRecursion.__default.AscendingChain#requires(LayerType, int) : bool;

// #requires axiom for CoRecursion.__default.AscendingChain
axiom (forall $ly: LayerType, n#0: int :: 
  { CoRecursion.__default.AscendingChain#requires($ly, n#0) } 
  CoRecursion.__default.AscendingChain#requires($ly, n#0) == true);

// definition axiom for CoRecursion.__default.AscendingChain (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    { CoRecursion.__default.AscendingChain($LS($ly), n#0) } 
    true
       ==> CoRecursion.__default.AscendingChain#canCall(n#0 + 1)
         && CoRecursion.__default.AscendingChain($LS($ly), n#0)
           == #CoRecursion.Stream.More($Box(n#0), CoRecursion.__default.AscendingChain($ly, n#0 + 1)));

// function declaration for CoRecursion._default.Prefix
function CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType)
   : DatatypeType;

function CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0: Ty, n#0: int, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), n#0, s#0) } 
  CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), n#0, s#0)
     == CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $ly, n#0, s#0));

// fuel synonym axiom
axiom (forall CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, AsFuelBottom($ly), n#0, s#0) } 
  CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $ly, n#0, s#0)
     == CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LZ, n#0, s#0));

// consequence axiom for CoRecursion.__default.Prefix
axiom true
   ==> (forall CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    { CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $ly, n#0, s#0) } 
    CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0, n#0, s#0)
         || (LitInt(0) <= n#0
           && $Is(s#0, Tclass.CoRecursion.Stream(CoRecursion._default.Prefix$_T0)))
       ==> $Is(CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $ly, n#0, s#0), 
        Tclass.CoRecursion.List(CoRecursion._default.Prefix$_T0)));

function CoRecursion.__default.Prefix#requires(Ty, LayerType, int, DatatypeType) : bool;

// #requires axiom for CoRecursion.__default.Prefix
axiom (forall CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { CoRecursion.__default.Prefix#requires(CoRecursion._default.Prefix$_T0, $ly, n#0, s#0) } 
  LitInt(0) <= n#0
       && $Is(s#0, Tclass.CoRecursion.Stream(CoRecursion._default.Prefix$_T0))
     ==> CoRecursion.__default.Prefix#requires(CoRecursion._default.Prefix$_T0, $ly, n#0, s#0)
       == true);

// definition axiom for CoRecursion.__default.Prefix (revealed)
axiom true
   ==> (forall CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    { CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), n#0, s#0) } 
    CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0, n#0, s#0)
         || (LitInt(0) <= n#0
           && $Is(s#0, Tclass.CoRecursion.Stream(CoRecursion._default.Prefix$_T0)))
       ==> (n#0 != LitInt(0)
           ==> CoRecursion.Stream.More_q(s#0)
             && 
            CoRecursion.Stream.More_q(s#0)
             && CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0, n#0 - 1, CoRecursion.Stream.rest(s#0)))
         && CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), n#0, s#0)
           == (if n#0 == LitInt(0)
             then #CoRecursion.List.Nil()
             else #CoRecursion.List.Cons(CoRecursion.Stream.head(s#0), 
              CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $ly, n#0 - 1, CoRecursion.Stream.rest(s#0)))));

// definition axiom for CoRecursion.__default.Prefix for decreasing-related literals (revealed)
axiom true
   ==> (forall CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    {:weight 3} { CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), LitInt(n#0), s#0) } 
    CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0, LitInt(n#0), s#0)
         || (LitInt(0) <= n#0
           && $Is(s#0, Tclass.CoRecursion.Stream(CoRecursion._default.Prefix$_T0)))
       ==> (LitInt(n#0) != LitInt(0)
           ==> CoRecursion.Stream.More_q(s#0)
             && 
            CoRecursion.Stream.More_q(s#0)
             && CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0, LitInt(n#0 - 1), CoRecursion.Stream.rest(s#0)))
         && CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), LitInt(n#0), s#0)
           == (if LitInt(n#0) == LitInt(0)
             then #CoRecursion.List.Nil()
             else #CoRecursion.List.Cons(CoRecursion.Stream.head(s#0), 
              CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, 
                $LS($ly), 
                LitInt(n#0 - 1), 
                CoRecursion.Stream.rest(s#0)))));

// definition axiom for CoRecursion.__default.Prefix for all literals (revealed)
axiom true
   ==> (forall CoRecursion._default.Prefix$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    {:weight 3} { CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), LitInt(n#0), Lit(s#0)) } 
    CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0, LitInt(n#0), Lit(s#0))
         || (LitInt(0) <= n#0
           && $Is(s#0, Tclass.CoRecursion.Stream(CoRecursion._default.Prefix$_T0)))
       ==> (LitInt(n#0) != LitInt(0)
           ==> CoRecursion.Stream.More_q(Lit(s#0))
             && 
            CoRecursion.Stream.More_q(Lit(s#0))
             && CoRecursion.__default.Prefix#canCall(CoRecursion._default.Prefix$_T0, 
              LitInt(n#0 - 1), 
              Lit(CoRecursion.Stream.rest(Lit(s#0)))))
         && CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, $LS($ly), LitInt(n#0), Lit(s#0))
           == (if LitInt(n#0) == LitInt(0)
             then #CoRecursion.List.Nil()
             else #CoRecursion.List.Cons(Lit(CoRecursion.Stream.head(Lit(s#0))), 
              Lit(CoRecursion.__default.Prefix(CoRecursion._default.Prefix$_T0, 
                  $LS($ly), 
                  LitInt(n#0 - 1), 
                  Lit(CoRecursion.Stream.rest(Lit(s#0))))))));

procedure CheckWellformed$$CoRecursion.__default.TestMain();
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$CoRecursion.__default.TestMain();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.S.C?: ClassName;

function Tclass.S.C?() : Ty;

const unique Tagclass.S.C?: TyTag;

// Tclass.S.C? Tag
axiom Tag(Tclass.S.C?()) == Tagclass.S.C? && TagFamily(Tclass.S.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.S.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.S.C?()) } 
  $IsBox(bx, Tclass.S.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.S.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.S.C?()) } 
  $Is($o, Tclass.S.C?()) <==> $o == null || dtype($o) == Tclass.S.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.S.C?(), $h) } 
  $IsAlloc($o, Tclass.S.C?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(S.C.f) == 0
   && FieldOfDecl(class.S.C?, field$f) == S.C.f
   && !$IsGhostField(S.C.f);

const S.C.f: Field int;

// C.f: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, S.C.f) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.S.C?()
     ==> $Is(read($h, $o, S.C.f), TInt));

// C.f: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, S.C.f) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.S.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, S.C.f), TInt, $h));

function Tclass.S.C() : Ty;

const unique Tagclass.S.C: TyTag;

// Tclass.S.C Tag
axiom Tag(Tclass.S.C()) == Tagclass.S.C && TagFamily(Tclass.S.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.S.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.S.C()) } 
  $IsBox(bx, Tclass.S.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.S.C()));

// S.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.S.C()) } 
  $Is(c#0, Tclass.S.C()) <==> $Is(c#0, Tclass.S.C?()) && c#0 != null);

// S.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.S.C(), $h) } 
  $IsAlloc(c#0, Tclass.S.C(), $h) <==> $IsAlloc(c#0, Tclass.S.C?(), $h));

const unique class.S.__default: ClassName;

function Tclass.S.__default() : Ty;

const unique Tagclass.S.__default: TyTag;

// Tclass.S.__default Tag
axiom Tag(Tclass.S.__default()) == Tagclass.S.__default
   && TagFamily(Tclass.S.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.S.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.S.__default()) } 
  $IsBox(bx, Tclass.S.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.S.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.S.__default()) } 
  $Is($o, Tclass.S.__default())
     <==> $o == null || dtype($o) == Tclass.S.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.S.__default(), $h) } 
  $IsAlloc($o, Tclass.S.__default(), $h) <==> $o == null || read($h, $o, alloc));

const unique class.T.C?: ClassName;

function Tclass.T.C?() : Ty;

const unique Tagclass.T.C?: TyTag;

// Tclass.T.C? Tag
axiom Tag(Tclass.T.C?()) == Tagclass.T.C? && TagFamily(Tclass.T.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.T.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.T.C?()) } 
  $IsBox(bx, Tclass.T.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.T.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.T.C?()) } 
  $Is($o, Tclass.T.C?()) <==> $o == null || dtype($o) == Tclass.T.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.T.C?(), $h) } 
  $IsAlloc($o, Tclass.T.C?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(T.C.f) == 0
   && FieldOfDecl(class.T.C?, field$f) == T.C.f
   && !$IsGhostField(T.C.f);

const T.C.f: Field int;

// C.f: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, T.C.f) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.T.C?()
     ==> $Is(read($h, $o, T.C.f), TInt));

// C.f: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, T.C.f) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.T.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, T.C.f), TInt, $h));

function Tclass.T.C() : Ty;

const unique Tagclass.T.C: TyTag;

// Tclass.T.C Tag
axiom Tag(Tclass.T.C()) == Tagclass.T.C && TagFamily(Tclass.T.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.T.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.T.C()) } 
  $IsBox(bx, Tclass.T.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.T.C()));

// T.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.T.C()) } 
  $Is(c#0, Tclass.T.C()) <==> $Is(c#0, Tclass.T.C?()) && c#0 != null);

// T.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.T.C(), $h) } 
  $IsAlloc(c#0, Tclass.T.C(), $h) <==> $IsAlloc(c#0, Tclass.T.C?(), $h));

const unique class.T.__default: ClassName;

function Tclass.T.__default() : Ty;

const unique Tagclass.T.__default: TyTag;

// Tclass.T.__default Tag
axiom Tag(Tclass.T.__default()) == Tagclass.T.__default
   && TagFamily(Tclass.T.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.T.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.T.__default()) } 
  $IsBox(bx, Tclass.T.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.T.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.T.__default()) } 
  $Is($o, Tclass.T.__default())
     <==> $o == null || dtype($o) == Tclass.T.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.T.__default(), $h) } 
  $IsAlloc($o, Tclass.T.__default(), $h) <==> $o == null || read($h, $o, alloc));

const unique class.A.__default: ClassName;

function Tclass.A.__default() : Ty;

const unique Tagclass.A.__default: TyTag;

// Tclass.A.__default Tag
axiom Tag(Tclass.A.__default()) == Tagclass.A.__default
   && TagFamily(Tclass.A.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.A.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A.__default()) } 
  $IsBox(bx, Tclass.A.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A.__default()) } 
  $Is($o, Tclass.A.__default())
     <==> $o == null || dtype($o) == Tclass.A.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A.__default(), $h) } 
  $IsAlloc($o, Tclass.A.__default(), $h) <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$A.__default.run();
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$A.__default.run();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.S1.__default: ClassName;

function Tclass.S1.__default() : Ty;

const unique Tagclass.S1.__default: TyTag;

// Tclass.S1.__default Tag
axiom Tag(Tclass.S1.__default()) == Tagclass.S1.__default
   && TagFamily(Tclass.S1.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.S1.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.S1.__default()) } 
  $IsBox(bx, Tclass.S1.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.S1.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.S1.__default()) } 
  $Is($o, Tclass.S1.__default())
     <==> $o == null || dtype($o) == Tclass.S1.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.S1.__default(), $h) } 
  $IsAlloc($o, Tclass.S1.__default(), $h) <==> $o == null || read($h, $o, alloc));

const unique class.T1.__default: ClassName;

function Tclass.T1.__default() : Ty;

const unique Tagclass.T1.__default: TyTag;

// Tclass.T1.__default Tag
axiom Tag(Tclass.T1.__default()) == Tagclass.T1.__default
   && TagFamily(Tclass.T1.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.T1.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.T1.__default()) } 
  $IsBox(bx, Tclass.T1.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.T1.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.T1.__default()) } 
  $Is($o, Tclass.T1.__default())
     <==> $o == null || dtype($o) == Tclass.T1.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.T1.__default(), $h) } 
  $IsAlloc($o, Tclass.T1.__default(), $h) <==> $o == null || read($h, $o, alloc));

const unique class.A1.__default: ClassName;

function Tclass.A1.__default() : Ty;

const unique Tagclass.A1.__default: TyTag;

// Tclass.A1.__default Tag
axiom Tag(Tclass.A1.__default()) == Tagclass.A1.__default
   && TagFamily(Tclass.A1.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.A1.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A1.__default()) } 
  $IsBox(bx, Tclass.A1.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A1.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A1.__default()) } 
  $Is($o, Tclass.A1.__default())
     <==> $o == null || dtype($o) == Tclass.A1.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A1.__default(), $h) } 
  $IsAlloc($o, Tclass.A1.__default(), $h) <==> $o == null || read($h, $o, alloc));

// Constructor function declaration
function #M.fixed.A() : DatatypeType;

const unique ##M.fixed.A: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#M.fixed.A()) == ##M.fixed.A;

function M.fixed.A_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { M.fixed.A_q(d) } 
  M.fixed.A_q(d) <==> DatatypeCtorId(d) == ##M.fixed.A);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { M.fixed.A_q(d) } 
  M.fixed.A_q(d) ==> d == #M.fixed.A());

function Tclass.M.fixed() : Ty;

const unique Tagclass.M.fixed: TyTag;

// Tclass.M.fixed Tag
axiom Tag(Tclass.M.fixed()) == Tagclass.M.fixed
   && TagFamily(Tclass.M.fixed()) == tytagFamily$fixed;

// Box/unbox axiom for Tclass.M.fixed
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M.fixed()) } 
  $IsBox(bx, Tclass.M.fixed())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.M.fixed()));

// Constructor $Is
axiom $Is(#M.fixed.A(), Tclass.M.fixed());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#M.fixed.A(), Tclass.M.fixed(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#M.fixed.A(), Tclass.M.fixed(), $h));

// Constructor literal
axiom #M.fixed.A() == Lit(#M.fixed.A());

// Constructor function declaration
function #M.fixed.B() : DatatypeType;

const unique ##M.fixed.B: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#M.fixed.B()) == ##M.fixed.B;

function M.fixed.B_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { M.fixed.B_q(d) } 
  M.fixed.B_q(d) <==> DatatypeCtorId(d) == ##M.fixed.B);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { M.fixed.B_q(d) } 
  M.fixed.B_q(d) ==> d == #M.fixed.B());

// Constructor $Is
axiom $Is(#M.fixed.B(), Tclass.M.fixed());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#M.fixed.B(), Tclass.M.fixed(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#M.fixed.B(), Tclass.M.fixed(), $h));

// Constructor literal
axiom #M.fixed.B() == Lit(#M.fixed.B());

// Depth-one case-split function
function $IsA#M.fixed(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#M.fixed(d) } 
  $IsA#M.fixed(d) ==> M.fixed.A_q(d) || M.fixed.B_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { M.fixed.B_q(d), $Is(d, Tclass.M.fixed()) } 
    { M.fixed.A_q(d), $Is(d, Tclass.M.fixed()) } 
  $Is(d, Tclass.M.fixed()) ==> M.fixed.A_q(d) || M.fixed.B_q(d));

// Datatype extensional equality declaration
function M.fixed#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #M.fixed.A
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M.fixed#Equal(a, b), M.fixed.A_q(a) } { M.fixed#Equal(a, b), M.fixed.A_q(b) } 
  M.fixed.A_q(a) && M.fixed.A_q(b) ==> (M.fixed#Equal(a, b) <==> true));

// Datatype extensional equality definition: #M.fixed.B
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M.fixed#Equal(a, b), M.fixed.B_q(a) } { M.fixed#Equal(a, b), M.fixed.B_q(b) } 
  M.fixed.B_q(a) && M.fixed.B_q(b) ==> (M.fixed#Equal(a, b) <==> true));

// Datatype extensionality axiom: M.fixed
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M.fixed#Equal(a, b) } 
  M.fixed#Equal(a, b) <==> a == b);

const unique class.M.fixed: ClassName;

const unique class.M.public?: ClassName;

function Tclass.M.public?() : Ty;

const unique Tagclass.M.public?: TyTag;

// Tclass.M.public? Tag
axiom Tag(Tclass.M.public?()) == Tagclass.M.public?
   && TagFamily(Tclass.M.public?()) == tytagFamily$public;

// Box/unbox axiom for Tclass.M.public?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M.public?()) } 
  $IsBox(bx, Tclass.M.public?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M.public?()));

// public: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M.public?()) } 
  $Is($o, Tclass.M.public?()) <==> $o == null || dtype($o) == Tclass.M.public?());

// public: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M.public?(), $h) } 
  $IsAlloc($o, Tclass.M.public?(), $h) <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$M.public.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass.M.public())
         && $IsAlloc(this, Tclass.M.public(), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M.public.__ctor()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass.M.public())
         && $IsAlloc(this, Tclass.M.public(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const M.public.private: Field int;

// public.private: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M.public.private) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M.public?()
     ==> $Is(read($h, $o, M.public.private), TInt));

// public.private: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M.public.private) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M.public?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M.public.private), TInt, $h));

// public.namespace: Type axiom
axiom (forall $o: ref :: { M.public.namespace($o) } $Is(M.public.namespace($o), TInt));

// public.namespace: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { M.public.namespace($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(M.public.namespace($o), TInt, $h));

// public.fallthrough: Type axiom
axiom (forall $o: ref :: 
  { M.public.fallthrough($o) } 
  $Is(M.public.fallthrough($o), TInt));

// public.fallthrough: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { M.public.fallthrough($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(M.public.fallthrough($o), TInt, $h));

// public.try: Type axiom
axiom (forall $o: ref :: { M.public.try($o) } $Is(M.public.try($o), TInt));

// public.try: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { M.public.try($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc) ==> $IsAlloc(M.public.try($o), TInt, $h));

// M.public: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.M.public()) } 
  $Is(c#0, Tclass.M.public()) <==> $Is(c#0, Tclass.M.public?()) && c#0 != null);

// M.public: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.M.public(), $h) } 
  $IsAlloc(c#0, Tclass.M.public(), $h) <==> $IsAlloc(c#0, Tclass.M.public?(), $h));

const unique class.M.__default: ClassName;

function Tclass.M.__default() : Ty;

const unique Tagclass.M.__default: TyTag;

// Tclass.M.__default Tag
axiom Tag(Tclass.M.__default()) == Tagclass.M.__default
   && TagFamily(Tclass.M.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.M.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M.__default()) } 
  $IsBox(bx, Tclass.M.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M.__default()) } 
  $Is($o, Tclass.M.__default())
     <==> $o == null || dtype($o) == Tclass.M.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M.__default(), $h) } 
  $IsAlloc($o, Tclass.M.__default(), $h) <==> $o == null || read($h, $o, alloc));

// function declaration for M._default.F
function M.__default.F() : DatatypeType;

function M.__default.F#canCall() : bool;

// consequence axiom for M.__default.F
axiom true ==> true ==> $Is(M.__default.F(), Tclass.M.fixed());

function M.__default.F#requires() : bool;

// #requires axiom for M.__default.F
axiom M.__default.F#requires() == true;

// definition axiom for M.__default.F (revealed)
axiom true ==> true ==> M.__default.F() == Lit(#M.fixed.A());

// definition axiom for M.__default.F for all literals (revealed)
axiom true ==> true ==> M.__default.F() == Lit(#M.fixed.A());

// Constructor function declaration
function #GhostLetExpr.Dt.MyRecord(int, int) : DatatypeType;

const unique ##GhostLetExpr.Dt.MyRecord: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: int, a#0#1#0: int :: 
  { #GhostLetExpr.Dt.MyRecord(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#GhostLetExpr.Dt.MyRecord(a#0#0#0, a#0#1#0))
     == ##GhostLetExpr.Dt.MyRecord);

function GhostLetExpr.Dt.MyRecord_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { GhostLetExpr.Dt.MyRecord_q(d) } 
  GhostLetExpr.Dt.MyRecord_q(d)
     <==> DatatypeCtorId(d) == ##GhostLetExpr.Dt.MyRecord);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { GhostLetExpr.Dt.MyRecord_q(d) } 
  GhostLetExpr.Dt.MyRecord_q(d)
     ==> (exists a#1#0#0: int, a#1#1#0: int :: 
      d == #GhostLetExpr.Dt.MyRecord(a#1#0#0, a#1#1#0)));

function Tclass.GhostLetExpr.Dt() : Ty;

const unique Tagclass.GhostLetExpr.Dt: TyTag;

// Tclass.GhostLetExpr.Dt Tag
axiom Tag(Tclass.GhostLetExpr.Dt()) == Tagclass.GhostLetExpr.Dt
   && TagFamily(Tclass.GhostLetExpr.Dt()) == tytagFamily$Dt;

// Box/unbox axiom for Tclass.GhostLetExpr.Dt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.GhostLetExpr.Dt()) } 
  $IsBox(bx, Tclass.GhostLetExpr.Dt())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.GhostLetExpr.Dt()));

// Constructor $Is
axiom (forall a#2#0#0: int, a#2#1#0: int :: 
  { $Is(#GhostLetExpr.Dt.MyRecord(a#2#0#0, a#2#1#0), Tclass.GhostLetExpr.Dt()) } 
  $Is(#GhostLetExpr.Dt.MyRecord(a#2#0#0, a#2#1#0), Tclass.GhostLetExpr.Dt())
     <==> $Is(a#2#0#0, TInt) && $Is(a#2#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#3#0#0: int, a#3#1#0: int, $h: Heap :: 
  { $IsAlloc(#GhostLetExpr.Dt.MyRecord(a#3#0#0, a#3#1#0), Tclass.GhostLetExpr.Dt(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#GhostLetExpr.Dt.MyRecord(a#3#0#0, a#3#1#0), Tclass.GhostLetExpr.Dt(), $h)
       <==> $IsAlloc(a#3#0#0, TInt, $h) && $IsAlloc(a#3#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(GhostLetExpr.Dt.a(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      GhostLetExpr.Dt.MyRecord_q(d)
       && $IsAlloc(d, Tclass.GhostLetExpr.Dt(), $h)
     ==> $IsAlloc(GhostLetExpr.Dt.a(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(GhostLetExpr.Dt.b(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      GhostLetExpr.Dt.MyRecord_q(d)
       && $IsAlloc(d, Tclass.GhostLetExpr.Dt(), $h)
     ==> $IsAlloc(GhostLetExpr.Dt.b(d), TInt, $h));

// Constructor literal
axiom (forall a#4#0#0: int, a#4#1#0: int :: 
  { #GhostLetExpr.Dt.MyRecord(LitInt(a#4#0#0), LitInt(a#4#1#0)) } 
  #GhostLetExpr.Dt.MyRecord(LitInt(a#4#0#0), LitInt(a#4#1#0))
     == Lit(#GhostLetExpr.Dt.MyRecord(a#4#0#0, a#4#1#0)));

function GhostLetExpr.Dt.a(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#5#0#0: int, a#5#1#0: int :: 
  { #GhostLetExpr.Dt.MyRecord(a#5#0#0, a#5#1#0) } 
  GhostLetExpr.Dt.a(#GhostLetExpr.Dt.MyRecord(a#5#0#0, a#5#1#0)) == a#5#0#0);

function GhostLetExpr.Dt.b(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#6#0#0: int, a#6#1#0: int :: 
  { #GhostLetExpr.Dt.MyRecord(a#6#0#0, a#6#1#0) } 
  GhostLetExpr.Dt.b(#GhostLetExpr.Dt.MyRecord(a#6#0#0, a#6#1#0)) == a#6#1#0);

// Depth-one case-split function
function $IsA#GhostLetExpr.Dt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#GhostLetExpr.Dt(d) } 
  $IsA#GhostLetExpr.Dt(d) ==> GhostLetExpr.Dt.MyRecord_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { GhostLetExpr.Dt.MyRecord_q(d), $Is(d, Tclass.GhostLetExpr.Dt()) } 
  $Is(d, Tclass.GhostLetExpr.Dt()) ==> GhostLetExpr.Dt.MyRecord_q(d));

// Datatype extensional equality declaration
function GhostLetExpr.Dt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #GhostLetExpr.Dt.MyRecord
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { GhostLetExpr.Dt#Equal(a, b) } 
  true
     ==> (GhostLetExpr.Dt#Equal(a, b)
       <==> GhostLetExpr.Dt.a(a) == GhostLetExpr.Dt.a(b)
         && GhostLetExpr.Dt.b(a) == GhostLetExpr.Dt.b(b)));

// Datatype extensionality axiom: GhostLetExpr.Dt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { GhostLetExpr.Dt#Equal(a, b) } 
  GhostLetExpr.Dt#Equal(a, b) <==> a == b);

const unique class.GhostLetExpr.Dt: ClassName;

const unique class.GhostLetExpr.__default: ClassName;

function Tclass.GhostLetExpr.__default() : Ty;

const unique Tagclass.GhostLetExpr.__default: TyTag;

// Tclass.GhostLetExpr.__default Tag
axiom Tag(Tclass.GhostLetExpr.__default()) == Tagclass.GhostLetExpr.__default
   && TagFamily(Tclass.GhostLetExpr.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.GhostLetExpr.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.GhostLetExpr.__default()) } 
  $IsBox(bx, Tclass.GhostLetExpr.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.GhostLetExpr.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.GhostLetExpr.__default()) } 
  $Is($o, Tclass.GhostLetExpr.__default())
     <==> $o == null || dtype($o) == Tclass.GhostLetExpr.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.GhostLetExpr.__default(), $h) } 
  $IsAlloc($o, Tclass.GhostLetExpr.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for GhostLetExpr._default.F
function GhostLetExpr.__default.F() : int;

function GhostLetExpr.__default.F#canCall() : bool;

// consequence axiom for GhostLetExpr.__default.F
axiom true ==> true ==> true;

function GhostLetExpr.__default.F#requires() : bool;

// #requires axiom for GhostLetExpr.__default.F
axiom GhostLetExpr.__default.F#requires() == true;

// definition axiom for GhostLetExpr.__default.F (revealed)
axiom true ==> true ==> GhostLetExpr.__default.F() == LitInt(5);

// definition axiom for GhostLetExpr.__default.F for all literals (revealed)
axiom true ==> true ==> GhostLetExpr.__default.F() == LitInt(5);

// function declaration for GhostLetExpr._default.G
function GhostLetExpr.__default.G(x#0: int, y#0: int) : int;

function GhostLetExpr.__default.G#canCall(x#0: int, y#0: int) : bool;

// consequence axiom for GhostLetExpr.__default.G
axiom true
   ==> (forall x#0: int, y#0: int :: 
    { GhostLetExpr.__default.G(x#0, y#0) } 
    true ==> true);

function GhostLetExpr.__default.G#requires(int, int) : bool;

// #requires axiom for GhostLetExpr.__default.G
axiom (forall x#0: int, y#0: int :: 
  { GhostLetExpr.__default.G#requires(x#0, y#0) } 
  GhostLetExpr.__default.G#requires(x#0, y#0) == true);

// definition axiom for GhostLetExpr.__default.G (revealed)
axiom true
   ==> (forall x#0: int, y#0: int :: 
    { GhostLetExpr.__default.G(x#0, y#0) } 
    true ==> GhostLetExpr.__default.G(x#0, y#0) == x#0);

// definition axiom for GhostLetExpr.__default.G for all literals (revealed)
axiom true
   ==> (forall x#0: int, y#0: int :: 
    {:weight 3} { GhostLetExpr.__default.G(LitInt(x#0), LitInt(y#0)) } 
    true ==> GhostLetExpr.__default.G(LitInt(x#0), LitInt(y#0)) == LitInt(x#0));

// function declaration for GhostLetExpr._default.FM
function GhostLetExpr.__default.FM() : int;

function GhostLetExpr.__default.FM#canCall() : bool;

// consequence axiom for GhostLetExpr.__default.FM
axiom true ==> true ==> true;

function GhostLetExpr.__default.FM#requires() : bool;

// #requires axiom for GhostLetExpr.__default.FM
axiom GhostLetExpr.__default.FM#requires() == true;

// definition axiom for GhostLetExpr.__default.FM (revealed)
axiom true
   ==> 
  true
   ==> GhostLetExpr.__default.F#canCall()
     && (var xyz#2 := LitInt(GhostLetExpr.__default.F()); 
      GhostLetExpr.__default.G#canCall(LitInt(5), xyz#2))
     && GhostLetExpr.__default.FM()
       == (var xyz#2 := LitInt(GhostLetExpr.__default.F()); 
        LitInt(GhostLetExpr.__default.G(LitInt(5), xyz#2)));

// definition axiom for GhostLetExpr.__default.FM for all literals (revealed)
axiom true
   ==> 
  true
   ==> GhostLetExpr.__default.F#canCall()
     && (var xyz#3 := LitInt(GhostLetExpr.__default.F()); 
      GhostLetExpr.__default.G#canCall(LitInt(5), xyz#3))
     && GhostLetExpr.__default.FM()
       == (var xyz#3 := LitInt(GhostLetExpr.__default.F()); 
        LitInt(GhostLetExpr.__default.G(LitInt(5), xyz#3)));

const unique class.EqualityTests.C?: ClassName;

function Tclass.EqualityTests.C?(Ty) : Ty;

const unique Tagclass.EqualityTests.C?: TyTag;

// Tclass.EqualityTests.C? Tag
axiom (forall EqualityTests.C$T: Ty :: 
  { Tclass.EqualityTests.C?(EqualityTests.C$T) } 
  Tag(Tclass.EqualityTests.C?(EqualityTests.C$T)) == Tagclass.EqualityTests.C?
     && TagFamily(Tclass.EqualityTests.C?(EqualityTests.C$T)) == tytagFamily$C);

// Tclass.EqualityTests.C? injectivity 0
axiom (forall EqualityTests.C$T: Ty :: 
  { Tclass.EqualityTests.C?(EqualityTests.C$T) } 
  Tclass.EqualityTests.C?_0(Tclass.EqualityTests.C?(EqualityTests.C$T))
     == EqualityTests.C$T);

function Tclass.EqualityTests.C?_0(Ty) : Ty;

// Box/unbox axiom for Tclass.EqualityTests.C?
axiom (forall EqualityTests.C$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.EqualityTests.C?(EqualityTests.C$T)) } 
  $IsBox(bx, Tclass.EqualityTests.C?(EqualityTests.C$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.EqualityTests.C?(EqualityTests.C$T)));

// C: Class $Is
axiom (forall EqualityTests.C$T: Ty, $o: ref :: 
  { $Is($o, Tclass.EqualityTests.C?(EqualityTests.C$T)) } 
  $Is($o, Tclass.EqualityTests.C?(EqualityTests.C$T))
     <==> $o == null || dtype($o) == Tclass.EqualityTests.C?(EqualityTests.C$T));

// C: Class $IsAlloc
axiom (forall EqualityTests.C$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.EqualityTests.C?(EqualityTests.C$T), $h) } 
  $IsAlloc($o, Tclass.EqualityTests.C?(EqualityTests.C$T), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.EqualityTests.C(Ty) : Ty;

const unique Tagclass.EqualityTests.C: TyTag;

// Tclass.EqualityTests.C Tag
axiom (forall EqualityTests.C$T: Ty :: 
  { Tclass.EqualityTests.C(EqualityTests.C$T) } 
  Tag(Tclass.EqualityTests.C(EqualityTests.C$T)) == Tagclass.EqualityTests.C
     && TagFamily(Tclass.EqualityTests.C(EqualityTests.C$T)) == tytagFamily$C);

// Tclass.EqualityTests.C injectivity 0
axiom (forall EqualityTests.C$T: Ty :: 
  { Tclass.EqualityTests.C(EqualityTests.C$T) } 
  Tclass.EqualityTests.C_0(Tclass.EqualityTests.C(EqualityTests.C$T))
     == EqualityTests.C$T);

function Tclass.EqualityTests.C_0(Ty) : Ty;

// Box/unbox axiom for Tclass.EqualityTests.C
axiom (forall EqualityTests.C$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.EqualityTests.C(EqualityTests.C$T)) } 
  $IsBox(bx, Tclass.EqualityTests.C(EqualityTests.C$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.EqualityTests.C(EqualityTests.C$T)));

// EqualityTests.C: subset type $Is
axiom (forall EqualityTests.C$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass.EqualityTests.C(EqualityTests.C$T)) } 
  $Is(c#0, Tclass.EqualityTests.C(EqualityTests.C$T))
     <==> $Is(c#0, Tclass.EqualityTests.C?(EqualityTests.C$T)) && c#0 != null);

// EqualityTests.C: subset type $IsAlloc
axiom (forall EqualityTests.C$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.EqualityTests.C(EqualityTests.C$T), $h) } 
  $IsAlloc(c#0, Tclass.EqualityTests.C(EqualityTests.C$T), $h)
     <==> $IsAlloc(c#0, Tclass.EqualityTests.C?(EqualityTests.C$T), $h));

const unique class.EqualityTests.__default: ClassName;

function Tclass.EqualityTests.__default() : Ty;

const unique Tagclass.EqualityTests.__default: TyTag;

// Tclass.EqualityTests.__default Tag
axiom Tag(Tclass.EqualityTests.__default()) == Tagclass.EqualityTests.__default
   && TagFamily(Tclass.EqualityTests.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.EqualityTests.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.EqualityTests.__default()) } 
  $IsBox(bx, Tclass.EqualityTests.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.EqualityTests.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.EqualityTests.__default()) } 
  $Is($o, Tclass.EqualityTests.__default())
     <==> $o == null || dtype($o) == Tclass.EqualityTests.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.EqualityTests.__default(), $h) } 
  $IsAlloc($o, Tclass.EqualityTests.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$EqualityTests.__default.TestMain();
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$EqualityTests.__default.TestMain();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.TypeInstantiations.GenCl?: ClassName;

function Tclass.TypeInstantiations.GenCl?(Ty) : Ty;

const unique Tagclass.TypeInstantiations.GenCl?: TyTag;

// Tclass.TypeInstantiations.GenCl? Tag
axiom (forall TypeInstantiations.GenCl$U: Ty :: 
  { Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U) } 
  Tag(Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U))
       == Tagclass.TypeInstantiations.GenCl?
     && TagFamily(Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U))
       == tytagFamily$GenCl);

// Tclass.TypeInstantiations.GenCl? injectivity 0
axiom (forall TypeInstantiations.GenCl$U: Ty :: 
  { Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U) } 
  Tclass.TypeInstantiations.GenCl?_0(Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U))
     == TypeInstantiations.GenCl$U);

function Tclass.TypeInstantiations.GenCl?_0(Ty) : Ty;

// Box/unbox axiom for Tclass.TypeInstantiations.GenCl?
axiom (forall TypeInstantiations.GenCl$U: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U)) } 
  $IsBox(bx, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U)));

// GenCl: Class $Is
axiom (forall TypeInstantiations.GenCl$U: Ty, $o: ref :: 
  { $Is($o, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U)) } 
  $Is($o, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U))
     <==> $o == null
       || dtype($o) == Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U));

// GenCl: Class $IsAlloc
axiom (forall TypeInstantiations.GenCl$U: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U), $h) } 
  $IsAlloc($o, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for TypeInstantiations.GenCl.Static
function TypeInstantiations.GenCl.Static(TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Static$G: Ty) : int;

function TypeInstantiations.GenCl.Static#canCall(TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Static$G: Ty) : bool;

// consequence axiom for TypeInstantiations.GenCl.Static
axiom true
   ==> (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Static$G: Ty :: 
    { TypeInstantiations.GenCl.Static(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Static$G) } 
    true ==> true);

function TypeInstantiations.GenCl.Static#requires(Ty, Ty) : bool;

// #requires axiom for TypeInstantiations.GenCl.Static
axiom (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Static$G: Ty :: 
  { TypeInstantiations.GenCl.Static#requires(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Static$G) } 
  TypeInstantiations.GenCl.Static#requires(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Static$G)
     == true);

// definition axiom for TypeInstantiations.GenCl.Static (revealed)
axiom true
   ==> (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Static$G: Ty :: 
    { TypeInstantiations.GenCl.Static(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Static$G) } 
    true
       ==> TypeInstantiations.GenCl.Static(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Static$G)
         == LitInt(58));

// definition axiom for TypeInstantiations.GenCl.Static for all literals (revealed)
axiom true
   ==> (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Static$G: Ty :: 
    {:weight 3} { TypeInstantiations.GenCl.Static(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Static$G) } 
    true
       ==> TypeInstantiations.GenCl.Static(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Static$G)
         == LitInt(58));

// function declaration for TypeInstantiations.GenCl.Inst
function TypeInstantiations.GenCl.Inst(TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Inst$G: Ty, this: ref)
   : int;

function TypeInstantiations.GenCl.Inst#canCall(TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Inst$G: Ty, this: ref)
   : bool;

function Tclass.TypeInstantiations.GenCl(Ty) : Ty;

const unique Tagclass.TypeInstantiations.GenCl: TyTag;

// Tclass.TypeInstantiations.GenCl Tag
axiom (forall TypeInstantiations.GenCl$U: Ty :: 
  { Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U) } 
  Tag(Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U))
       == Tagclass.TypeInstantiations.GenCl
     && TagFamily(Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U))
       == tytagFamily$GenCl);

// Tclass.TypeInstantiations.GenCl injectivity 0
axiom (forall TypeInstantiations.GenCl$U: Ty :: 
  { Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U) } 
  Tclass.TypeInstantiations.GenCl_0(Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U))
     == TypeInstantiations.GenCl$U);

function Tclass.TypeInstantiations.GenCl_0(Ty) : Ty;

// Box/unbox axiom for Tclass.TypeInstantiations.GenCl
axiom (forall TypeInstantiations.GenCl$U: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U)) } 
  $IsBox(bx, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U)));

// consequence axiom for TypeInstantiations.GenCl.Inst
axiom true
   ==> (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Inst$G: Ty, this: ref :: 
    { TypeInstantiations.GenCl.Inst(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, this) } 
    TypeInstantiations.GenCl.Inst#canCall(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, this)
         || (this != null
           && $Is(this, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U)))
       ==> true);

function TypeInstantiations.GenCl.Inst#requires(Ty, Ty, ref) : bool;

// #requires axiom for TypeInstantiations.GenCl.Inst
axiom (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Inst$G: Ty, this: ref :: 
  { TypeInstantiations.GenCl.Inst#requires(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, this) } 
  this != null
       && $Is(this, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U))
     ==> TypeInstantiations.GenCl.Inst#requires(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, this)
       == true);

// definition axiom for TypeInstantiations.GenCl.Inst (revealed)
axiom true
   ==> (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Inst$G: Ty, this: ref :: 
    { TypeInstantiations.GenCl.Inst(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, this) } 
    TypeInstantiations.GenCl.Inst#canCall(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, this)
         || (this != null
           && $Is(this, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U)))
       ==> TypeInstantiations.GenCl.Inst(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, this)
         == LitInt(59));

// definition axiom for TypeInstantiations.GenCl.Inst for all literals (revealed)
axiom true
   ==> (forall TypeInstantiations.GenCl$U: Ty, TypeInstantiations.GenCl.Inst$G: Ty, this: ref :: 
    {:weight 3} { TypeInstantiations.GenCl.Inst(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, Lit(this)) } 
    TypeInstantiations.GenCl.Inst#canCall(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, Lit(this))
         || (this != null
           && $Is(this, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U)))
       ==> TypeInstantiations.GenCl.Inst(TypeInstantiations.GenCl$U, TypeInstantiations.GenCl.Inst$G, Lit(this))
         == LitInt(59));

// TypeInstantiations.GenCl: subset type $Is
axiom (forall TypeInstantiations.GenCl$U: Ty, c#0: ref :: 
  { $Is(c#0, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U)) } 
  $Is(c#0, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U))
     <==> $Is(c#0, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U))
       && c#0 != null);

// TypeInstantiations.GenCl: subset type $IsAlloc
axiom (forall TypeInstantiations.GenCl$U: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U), $h) } 
  $IsAlloc(c#0, Tclass.TypeInstantiations.GenCl(TypeInstantiations.GenCl$U), $h)
     <==> $IsAlloc(c#0, Tclass.TypeInstantiations.GenCl?(TypeInstantiations.GenCl$U), $h));

const unique class.TypeInstantiations.__default: ClassName;

function Tclass.TypeInstantiations.__default() : Ty;

const unique Tagclass.TypeInstantiations.__default: TyTag;

// Tclass.TypeInstantiations.__default Tag
axiom Tag(Tclass.TypeInstantiations.__default())
     == Tagclass.TypeInstantiations.__default
   && TagFamily(Tclass.TypeInstantiations.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TypeInstantiations.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TypeInstantiations.__default()) } 
  $IsBox(bx, Tclass.TypeInstantiations.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TypeInstantiations.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TypeInstantiations.__default()) } 
  $Is($o, Tclass.TypeInstantiations.__default())
     <==> $o == null || dtype($o) == Tclass.TypeInstantiations.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TypeInstantiations.__default(), $h) } 
  $IsAlloc($o, Tclass.TypeInstantiations.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for TypeInstantiations._default.F
function TypeInstantiations.__default.F(TypeInstantiations._default.F$G: Ty) : int;

function TypeInstantiations.__default.F#canCall(TypeInstantiations._default.F$G: Ty) : bool;

// consequence axiom for TypeInstantiations.__default.F
axiom true
   ==> (forall TypeInstantiations._default.F$G: Ty :: 
    { TypeInstantiations.__default.F(TypeInstantiations._default.F$G) } 
    true ==> true);

function TypeInstantiations.__default.F#requires(Ty) : bool;

// #requires axiom for TypeInstantiations.__default.F
axiom (forall TypeInstantiations._default.F$G: Ty :: 
  { TypeInstantiations.__default.F#requires(TypeInstantiations._default.F$G) } 
  TypeInstantiations.__default.F#requires(TypeInstantiations._default.F$G) == true);

// definition axiom for TypeInstantiations.__default.F (revealed)
axiom true
   ==> (forall TypeInstantiations._default.F$G: Ty :: 
    { TypeInstantiations.__default.F(TypeInstantiations._default.F$G) } 
    true
       ==> TypeInstantiations.__default.F(TypeInstantiations._default.F$G) == LitInt(56));

// definition axiom for TypeInstantiations.__default.F for all literals (revealed)
axiom true
   ==> (forall TypeInstantiations._default.F$G: Ty :: 
    {:weight 3} { TypeInstantiations.__default.F(TypeInstantiations._default.F$G) } 
    true
       ==> TypeInstantiations.__default.F(TypeInstantiations._default.F$G) == LitInt(56));

// function declaration for TypeInstantiations._default.H
function TypeInstantiations.__default.H(TypeInstantiations._default.H$G: Ty, g#0: Box) : int;

function TypeInstantiations.__default.H#canCall(TypeInstantiations._default.H$G: Ty, g#0: Box) : bool;

// consequence axiom for TypeInstantiations.__default.H
axiom true
   ==> (forall TypeInstantiations._default.H$G: Ty, g#0: Box :: 
    { TypeInstantiations.__default.H(TypeInstantiations._default.H$G, g#0) } 
    TypeInstantiations.__default.H#canCall(TypeInstantiations._default.H$G, g#0)
         || $IsBox(g#0, TypeInstantiations._default.H$G)
       ==> true);

function TypeInstantiations.__default.H#requires(Ty, Box) : bool;

// #requires axiom for TypeInstantiations.__default.H
axiom (forall TypeInstantiations._default.H$G: Ty, g#0: Box :: 
  { TypeInstantiations.__default.H#requires(TypeInstantiations._default.H$G, g#0) } 
  $IsBox(g#0, TypeInstantiations._default.H$G)
     ==> TypeInstantiations.__default.H#requires(TypeInstantiations._default.H$G, g#0)
       == true);

// definition axiom for TypeInstantiations.__default.H (revealed)
axiom true
   ==> (forall TypeInstantiations._default.H$G: Ty, g#0: Box :: 
    { TypeInstantiations.__default.H(TypeInstantiations._default.H$G, g#0) } 
    TypeInstantiations.__default.H#canCall(TypeInstantiations._default.H$G, g#0)
         || $IsBox(g#0, TypeInstantiations._default.H$G)
       ==> TypeInstantiations.__default.H(TypeInstantiations._default.H$G, g#0)
         == LitInt(57));

// definition axiom for TypeInstantiations.__default.H for all literals (revealed)
axiom true
   ==> (forall TypeInstantiations._default.H$G: Ty, g#0: Box :: 
    {:weight 3} { TypeInstantiations.__default.H(TypeInstantiations._default.H$G, Lit(g#0)) } 
    TypeInstantiations.__default.H#canCall(TypeInstantiations._default.H$G, Lit(g#0))
         || $IsBox(g#0, TypeInstantiations._default.H$G)
       ==> TypeInstantiations.__default.H(TypeInstantiations._default.H$G, Lit(g#0))
         == LitInt(57));

procedure CheckWellformed$$TypeInstantiations.__default.TestMain();
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TypeInstantiations.__default.TestMain();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.TailRecursionWhereTypeParametersChange.__default: ClassName;

function Tclass.TailRecursionWhereTypeParametersChange.__default() : Ty;

const unique Tagclass.TailRecursionWhereTypeParametersChange.__default: TyTag;

// Tclass.TailRecursionWhereTypeParametersChange.__default Tag
axiom Tag(Tclass.TailRecursionWhereTypeParametersChange.__default())
     == Tagclass.TailRecursionWhereTypeParametersChange.__default
   && TagFamily(Tclass.TailRecursionWhereTypeParametersChange.__default())
     == tytagFamily$_default;

// Box/unbox axiom for Tclass.TailRecursionWhereTypeParametersChange.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TailRecursionWhereTypeParametersChange.__default()) } 
  $IsBox(bx, Tclass.TailRecursionWhereTypeParametersChange.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TailRecursionWhereTypeParametersChange.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TailRecursionWhereTypeParametersChange.__default()) } 
  $Is($o, Tclass.TailRecursionWhereTypeParametersChange.__default())
     <==> $o == null
       || dtype($o) == Tclass.TailRecursionWhereTypeParametersChange.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TailRecursionWhereTypeParametersChange.__default(), $h) } 
  $IsAlloc($o, Tclass.TailRecursionWhereTypeParametersChange.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$TailRecursionWhereTypeParametersChange.__default.TestMain();
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TailRecursionWhereTypeParametersChange.__default.TestMain();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.GeneralMaps.__default: ClassName;

function Tclass.GeneralMaps.__default() : Ty;

const unique Tagclass.GeneralMaps.__default: TyTag;

// Tclass.GeneralMaps.__default Tag
axiom Tag(Tclass.GeneralMaps.__default()) == Tagclass.GeneralMaps.__default
   && TagFamily(Tclass.GeneralMaps.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.GeneralMaps.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.GeneralMaps.__default()) } 
  $IsBox(bx, Tclass.GeneralMaps.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.GeneralMaps.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.GeneralMaps.__default()) } 
  $Is($o, Tclass.GeneralMaps.__default())
     <==> $o == null || dtype($o) == Tclass.GeneralMaps.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.GeneralMaps.__default(), $h) } 
  $IsAlloc($o, Tclass.GeneralMaps.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$GeneralMaps.__default.Test();
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$GeneralMaps.__default.Test();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.Cardinalities.__default: ClassName;

function Tclass.Cardinalities.__default() : Ty;

const unique Tagclass.Cardinalities.__default: TyTag;

// Tclass.Cardinalities.__default Tag
axiom Tag(Tclass.Cardinalities.__default()) == Tagclass.Cardinalities.__default
   && TagFamily(Tclass.Cardinalities.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.Cardinalities.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.Cardinalities.__default()) } 
  $IsBox(bx, Tclass.Cardinalities.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.Cardinalities.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.Cardinalities.__default()) } 
  $Is($o, Tclass.Cardinalities.__default())
     <==> $o == null || dtype($o) == Tclass.Cardinalities.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.Cardinalities.__default(), $h) } 
  $IsAlloc($o, Tclass.Cardinalities.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$Cardinalities.__default.Test();
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$Cardinalities.__default.Test();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.AltLoop.__default: ClassName;

function Tclass.AltLoop.__default() : Ty;

const unique Tagclass.AltLoop.__default: TyTag;

// Tclass.AltLoop.__default Tag
axiom Tag(Tclass.AltLoop.__default()) == Tagclass.AltLoop.__default
   && TagFamily(Tclass.AltLoop.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.AltLoop.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AltLoop.__default()) } 
  $IsBox(bx, Tclass.AltLoop.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.AltLoop.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.AltLoop.__default()) } 
  $Is($o, Tclass.AltLoop.__default())
     <==> $o == null || dtype($o) == Tclass.AltLoop.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AltLoop.__default(), $h) } 
  $IsAlloc($o, Tclass.AltLoop.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$AltLoop.__default.Test();
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$AltLoop.__default.Test();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const class.S1.B.Abs.__default: ClassName;

function Tclass.S1.B.Abs.__default() : Ty;

// Tclass.S1.B.Abs.__default Tag
axiom TagFamily(Tclass.S1.B.Abs.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.S1.B.Abs.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.S1.B.Abs.__default()) } 
  $IsBox(bx, Tclass.S1.B.Abs.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.S1.B.Abs.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.S1.B.Abs.__default()) } 
  $Is($o, Tclass.S1.B.Abs.__default())
     <==> $o == null || dtype($o) == Tclass.S1.B.Abs.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.S1.B.Abs.__default(), $h) } 
  $IsAlloc($o, Tclass.S1.B.Abs.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const class.S1.B.Abs.C?: ClassName;

function Tclass.S1.B.Abs.C?() : Ty;

// Tclass.S1.B.Abs.C? Tag
axiom TagFamily(Tclass.S1.B.Abs.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.S1.B.Abs.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.S1.B.Abs.C?()) } 
  $IsBox(bx, Tclass.S1.B.Abs.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.S1.B.Abs.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.S1.B.Abs.C?()) } 
  $Is($o, Tclass.S1.B.Abs.C?())
     <==> $o == null || dtype($o) == Tclass.S1.B.Abs.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.S1.B.Abs.C?(), $h) } 
  $IsAlloc($o, Tclass.S1.B.Abs.C?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(S1.B.Abs.C.f) == 0
   && FieldOfDecl(class.S1.B.Abs.C?, field$f) == S1.B.Abs.C.f
   && !$IsGhostField(S1.B.Abs.C.f);

const S1.B.Abs.C.f: Field int;

// C.f: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, S1.B.Abs.C.f) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.S1.B.Abs.C?()
     ==> $Is(read($h, $o, S1.B.Abs.C.f), TInt));

// C.f: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, S1.B.Abs.C.f) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.S1.B.Abs.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, S1.B.Abs.C.f), TInt, $h));

function Tclass.S1.B.Abs.C() : Ty;

// Tclass.S1.B.Abs.C Tag
axiom TagFamily(Tclass.S1.B.Abs.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.S1.B.Abs.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.S1.B.Abs.C()) } 
  $IsBox(bx, Tclass.S1.B.Abs.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.S1.B.Abs.C()));

// S1.B.Abs.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.S1.B.Abs.C()) } 
  $Is(c#0, Tclass.S1.B.Abs.C()) <==> $Is(c#0, Tclass.S1.B.Abs.C?()) && c#0 != null);

// S1.B.Abs.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.S1.B.Abs.C(), $h) } 
  $IsAlloc(c#0, Tclass.S1.B.Abs.C(), $h)
     <==> $IsAlloc(c#0, Tclass.S1.B.Abs.C?(), $h));

const class.A1.X.B.Abs.__default: ClassName;

function Tclass.A1.X.B.Abs.__default() : Ty;

// Tclass.A1.X.B.Abs.__default Tag
axiom TagFamily(Tclass.A1.X.B.Abs.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.A1.X.B.Abs.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A1.X.B.Abs.__default()) } 
  $IsBox(bx, Tclass.A1.X.B.Abs.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.A1.X.B.Abs.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A1.X.B.Abs.__default()) } 
  $Is($o, Tclass.A1.X.B.Abs.__default())
     <==> $o == null || dtype($o) == Tclass.A1.X.B.Abs.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A1.X.B.Abs.__default(), $h) } 
  $IsAlloc($o, Tclass.A1.X.B.Abs.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const class.A1.X.B.Abs.C?: ClassName;

function Tclass.A1.X.B.Abs.C?() : Ty;

// Tclass.A1.X.B.Abs.C? Tag
axiom TagFamily(Tclass.A1.X.B.Abs.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.A1.X.B.Abs.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A1.X.B.Abs.C?()) } 
  $IsBox(bx, Tclass.A1.X.B.Abs.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A1.X.B.Abs.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A1.X.B.Abs.C?()) } 
  $Is($o, Tclass.A1.X.B.Abs.C?())
     <==> $o == null || dtype($o) == Tclass.A1.X.B.Abs.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A1.X.B.Abs.C?(), $h) } 
  $IsAlloc($o, Tclass.A1.X.B.Abs.C?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(A1.X.B.Abs.C.f) == 0
   && FieldOfDecl(class.A1.X.B.Abs.C?, field$f) == A1.X.B.Abs.C.f
   && !$IsGhostField(A1.X.B.Abs.C.f);

const A1.X.B.Abs.C.f: Field int;

// C.f: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, A1.X.B.Abs.C.f) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.A1.X.B.Abs.C?()
     ==> $Is(read($h, $o, A1.X.B.Abs.C.f), TInt));

// C.f: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, A1.X.B.Abs.C.f) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.A1.X.B.Abs.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, A1.X.B.Abs.C.f), TInt, $h));

function Tclass.A1.X.B.Abs.C() : Ty;

// Tclass.A1.X.B.Abs.C Tag
axiom TagFamily(Tclass.A1.X.B.Abs.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.A1.X.B.Abs.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A1.X.B.Abs.C()) } 
  $IsBox(bx, Tclass.A1.X.B.Abs.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A1.X.B.Abs.C()));

// A1.X.B.Abs.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.A1.X.B.Abs.C()) } 
  $Is(c#0, Tclass.A1.X.B.Abs.C())
     <==> $Is(c#0, Tclass.A1.X.B.Abs.C?()) && c#0 != null);

// A1.X.B.Abs.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.A1.X.B.Abs.C(), $h) } 
  $IsAlloc(c#0, Tclass.A1.X.B.Abs.C(), $h)
     <==> $IsAlloc(c#0, Tclass.A1.X.B.Abs.C?(), $h));

const class.A1.X.Abs.__default: ClassName;

function Tclass.A1.X.Abs.__default() : Ty;

// Tclass.A1.X.Abs.__default Tag
axiom TagFamily(Tclass.A1.X.Abs.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.A1.X.Abs.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A1.X.Abs.__default()) } 
  $IsBox(bx, Tclass.A1.X.Abs.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A1.X.Abs.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A1.X.Abs.__default()) } 
  $Is($o, Tclass.A1.X.Abs.__default())
     <==> $o == null || dtype($o) == Tclass.A1.X.Abs.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A1.X.Abs.__default(), $h) } 
  $IsAlloc($o, Tclass.A1.X.Abs.__default(), $h)
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

const unique tytagFamily$Tuple: TyTagFamily;

const unique tytagFamily$DigitsClass: TyTagFamily;

const unique tytagFamily$DigitUnderscore_Names: TyTagFamily;

const unique tytagFamily$DigitUnderscore_Names_Functions_and_Methods: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$public: TyTagFamily;

const unique tytagFamily$MyDt: TyTagFamily;

const unique tytagFamily$Stream: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Cell: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$fixed: TyTagFamily;

const unique tytagFamily$Dt: TyTagFamily;

const unique tytagFamily$GenCl: TyTagFamily;

const unique field$7: NameFamily;

const unique field$0_1_0: NameFamily;

const unique field$010: NameFamily;

const unique field$10: NameFamily;

const unique field$private: NameFamily;

const unique field$data: NameFamily;

const unique field$f: NameFamily;
