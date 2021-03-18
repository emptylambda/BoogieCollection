// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy -print:./Twostate-Verification.bpl

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

// Box/unbox axiom for bv19
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(19)) } 
  $IsBox(bx, TBitvector(19))
     ==> $Box($Unbox(bx): bv19) == bx && $Is($Unbox(bx): bv19, TBitvector(19)));

axiom (forall v: bv19 :: { $Is(v, TBitvector(19)) } $Is(v, TBitvector(19)));

axiom (forall v: bv19, heap: Heap :: 
  { $IsAlloc(v, TBitvector(19), heap) } 
  $IsAlloc(v, TBitvector(19), heap));

function {:bvbuiltin "bvand"} and_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvor"} or_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvxor"} xor_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvnot"} not_bv19(bv19) : bv19;

function {:bvbuiltin "bvadd"} add_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvsub"} sub_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvmul"} mul_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvudiv"} div_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvurem"} mod_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvult"} lt_bv19(bv19, bv19) : bool;

function {:bvbuiltin "bvule"} le_bv19(bv19, bv19) : bool;

function {:bvbuiltin "bvuge"} ge_bv19(bv19, bv19) : bool;

function {:bvbuiltin "bvugt"} gt_bv19(bv19, bv19) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "bvlshr"} RightShift_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv19(bv19, bv19) : bv19;

function {:bvbuiltin "(_ int2bv 19)"} nat_to_bv19(int) : bv19;

function {:bvbuiltin "bv2int"} smt_nat_from_bv19(bv19) : int;

function nat_from_bv19(bv19) : int;

axiom (forall b: bv19 :: 
  { nat_from_bv19(b) } 
  0 <= nat_from_bv19(b)
     && nat_from_bv19(b) < 524288
     && nat_from_bv19(b) == smt_nat_from_bv19(b));

// Box/unbox axiom for bv3
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(3)) } 
  $IsBox(bx, TBitvector(3))
     ==> $Box($Unbox(bx): bv3) == bx && $Is($Unbox(bx): bv3, TBitvector(3)));

axiom (forall v: bv3 :: { $Is(v, TBitvector(3)) } $Is(v, TBitvector(3)));

axiom (forall v: bv3, heap: Heap :: 
  { $IsAlloc(v, TBitvector(3), heap) } 
  $IsAlloc(v, TBitvector(3), heap));

function {:bvbuiltin "bvand"} and_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvor"} or_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvxor"} xor_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvnot"} not_bv3(bv3) : bv3;

function {:bvbuiltin "bvadd"} add_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvsub"} sub_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvmul"} mul_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvudiv"} div_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvurem"} mod_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvult"} lt_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvule"} le_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvuge"} ge_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvugt"} gt_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvlshr"} RightShift_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "(_ int2bv 3)"} nat_to_bv3(int) : bv3;

function {:bvbuiltin "bv2int"} smt_nat_from_bv3(bv3) : int;

function nat_from_bv3(bv3) : int;

axiom (forall b: bv3 :: 
  { nat_from_bv3(b) } 
  0 <= nat_from_bv3(b)
     && nat_from_bv3(b) < 8
     && nat_from_bv3(b) == smt_nat_from_bv3(b));

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

const BaseFuel_TwoStateAt._default.Opaque: LayerType;

const StartFuel_TwoStateAt._default.Opaque: LayerType;

const StartFuelAssert_TwoStateAt._default.Opaque: LayerType;

const unique class.TwoStateAt.Cell?: ClassName;

function Tclass.TwoStateAt.Cell?() : Ty;

const unique Tagclass.TwoStateAt.Cell?: TyTag;

// Tclass.TwoStateAt.Cell? Tag
axiom Tag(Tclass.TwoStateAt.Cell?()) == Tagclass.TwoStateAt.Cell?
   && TagFamily(Tclass.TwoStateAt.Cell?()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.TwoStateAt.Cell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TwoStateAt.Cell?()) } 
  $IsBox(bx, Tclass.TwoStateAt.Cell?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.TwoStateAt.Cell?()));

// Cell: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TwoStateAt.Cell?()) } 
  $Is($o, Tclass.TwoStateAt.Cell?())
     <==> $o == null || dtype($o) == Tclass.TwoStateAt.Cell?());

// Cell: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TwoStateAt.Cell?(), $h) } 
  $IsAlloc($o, Tclass.TwoStateAt.Cell?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(TwoStateAt.Cell.data) == 0
   && FieldOfDecl(class.TwoStateAt.Cell?, field$data) == TwoStateAt.Cell.data
   && !$IsGhostField(TwoStateAt.Cell.data);

const TwoStateAt.Cell.data: Field int;

// Cell.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, TwoStateAt.Cell.data) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.TwoStateAt.Cell?()
     ==> $Is(read($h, $o, TwoStateAt.Cell.data), TInt));

// Cell.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, TwoStateAt.Cell.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.TwoStateAt.Cell?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, TwoStateAt.Cell.data), TInt, $h));

function Tclass.TwoStateAt.Cell() : Ty;

const unique Tagclass.TwoStateAt.Cell: TyTag;

// Tclass.TwoStateAt.Cell Tag
axiom Tag(Tclass.TwoStateAt.Cell()) == Tagclass.TwoStateAt.Cell
   && TagFamily(Tclass.TwoStateAt.Cell()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.TwoStateAt.Cell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TwoStateAt.Cell()) } 
  $IsBox(bx, Tclass.TwoStateAt.Cell())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.TwoStateAt.Cell()));

procedure CheckWellformed$$TwoStateAt.Cell.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass.TwoStateAt.Cell())
         && $IsAlloc(this, Tclass.TwoStateAt.Cell(), $Heap), 
    x#0: int);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.Cell.__ctor(x#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass.TwoStateAt.Cell())
         && $IsAlloc(this, Tclass.TwoStateAt.Cell(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, TwoStateAt.Cell.data) == x#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.Cell.__ctor(x#0: int)
   returns (this: ref where this != null && $Is(this, Tclass.TwoStateAt.Cell()), 
    $_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, TwoStateAt.Cell.data) == x#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.Cell.__ctor(x#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.data: int;

    // AddMethodImpl: _ctor, Impl$$TwoStateAt.Cell.__ctor
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(246,4): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(246,5)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(247,12)
    assume true;
    assume true;
    this.data := x#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(247,15)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(246,5)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, TwoStateAt.Cell.data) == this.data;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(246,5)
}



// function declaration for TwoStateAt.Cell.Sum
function TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y: Ty, $prevHeap: Heap, $heap: Heap, c#0: ref, y#0: Box)
   : int;

function TwoStateAt.Cell.Sum#canCall(TwoStateAt.Cell.Sum$Y: Ty, $prevHeap: Heap, $heap: Heap, c#0: ref, y#0: Box)
   : bool;

// frame axiom for TwoStateAt.Cell.Sum
axiom (forall TwoStateAt.Cell.Sum$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    c#0: ref, 
    y#0: Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, $prevHeap, $h1, c#0, y#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.Cell.Sum#canCall(TwoStateAt.Cell.Sum$Y, $prevHeap, $h0, c#0, y#0)
         || ($Is(c#0, Tclass.TwoStateAt.Cell()) && $IsBox(y#0, TwoStateAt.Cell.Sum$Y)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, $prevHeap, $h0, c#0, y#0)
       == TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, $prevHeap, $h1, c#0, y#0));

// consequence axiom for TwoStateAt.Cell.Sum
axiom 3 <= $FunctionContextHeight
   ==> (forall TwoStateAt.Cell.Sum$Y: Ty, $prevHeap: Heap, $Heap: Heap, c#0: ref, y#0: Box :: 
    { TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0) } 
    TwoStateAt.Cell.Sum#canCall(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell())
           && $IsBox(y#0, TwoStateAt.Cell.Sum$Y))
       ==> true);

function TwoStateAt.Cell.Sum#requires(Ty, Heap, Heap, ref, Box) : bool;

// #requires axiom for TwoStateAt.Cell.Sum
axiom (forall TwoStateAt.Cell.Sum$Y: Ty, $prevHeap: Heap, $Heap: Heap, c#0: ref, y#0: Box :: 
  { TwoStateAt.Cell.Sum#requires(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsBox(y#0, TwoStateAt.Cell.Sum$Y)
     ==> TwoStateAt.Cell.Sum#requires(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0)
       == ($IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)
         && $IsAllocBox(y#0, TwoStateAt.Cell.Sum$Y, $prevHeap)));

// definition axiom for TwoStateAt.Cell.Sum (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall TwoStateAt.Cell.Sum$Y: Ty, $prevHeap: Heap, $Heap: Heap, c#0: ref, y#0: Box :: 
    { TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0), $IsGoodHeap($Heap) } 
    TwoStateAt.Cell.Sum#canCall(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell())
           && $IsBox(y#0, TwoStateAt.Cell.Sum$Y))
       ==> TwoStateAt.Cell.Plus#canCall(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0)
         && TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0)
           == TwoStateAt.Cell.Plus(TwoStateAt.Cell.Sum$Y, $prevHeap, $Heap, c#0, y#0));

procedure CheckWellformed$$TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.Sum$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.Sum$Y, previous$Heap));
  free requires 3 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref, 
    y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##y#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Sum
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(250,29): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assert c#0 != null;
        ##y#0 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#0, TwoStateAt.Cell.Sum$Y, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert $IsAllocBox(y#0, TwoStateAt.Cell.Sum$Y, old($Heap));
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == c#0 ==> $_Frame[$o, $f]);
        assume TwoStateAt.Cell.Plus#canCall(TwoStateAt.Cell.Sum$Y, old($Heap), $Heap, c#0, y#0);
        assume TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, old($Heap), $Heap, c#0, y#0)
           == TwoStateAt.Cell.Plus(TwoStateAt.Cell.Sum$Y, old($Heap), $Heap, c#0, y#0);
        assume TwoStateAt.Cell.Plus#canCall(TwoStateAt.Cell.Sum$Y, old($Heap), $Heap, c#0, y#0);
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.Cell.Sum(TwoStateAt.Cell.Sum$Y, old($Heap), $Heap, c#0, y#0), TInt);
        assert b$reqreads#0;
    }
}



// function declaration for TwoStateAt.Cell.Plus
function TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y: Ty, $prevHeap: Heap, $heap: Heap, this: ref, y#0: Box)
   : int;

function TwoStateAt.Cell.Plus#canCall(TwoStateAt.Cell.Plus$Y: Ty, $prevHeap: Heap, $heap: Heap, this: ref, y#0: Box)
   : bool;

// frame axiom for TwoStateAt.Cell.Plus
axiom (forall TwoStateAt.Cell.Plus$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    this: ref, 
    y#0: Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $h1, this, y#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.TwoStateAt.Cell())
       && (TwoStateAt.Cell.Plus#canCall(TwoStateAt.Cell.Plus$Y, $prevHeap, $h0, this, y#0)
         || $IsBox(y#0, TwoStateAt.Cell.Plus$Y))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $h0, this, y#0)
       == TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $h1, this, y#0));

// consequence axiom for TwoStateAt.Cell.Plus
axiom 2 <= $FunctionContextHeight
   ==> (forall TwoStateAt.Cell.Plus$Y: Ty, $prevHeap: Heap, $Heap: Heap, this: ref, y#0: Box :: 
    { TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0) } 
    TwoStateAt.Cell.Plus#canCall(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.TwoStateAt.Cell())
           && $IsAlloc(this, Tclass.TwoStateAt.Cell(), $prevHeap)
           && $IsBox(y#0, TwoStateAt.Cell.Plus$Y))
       ==> true);

function TwoStateAt.Cell.Plus#requires(Ty, Heap, Heap, ref, Box) : bool;

// #requires axiom for TwoStateAt.Cell.Plus
axiom (forall TwoStateAt.Cell.Plus$Y: Ty, $prevHeap: Heap, $Heap: Heap, this: ref, y#0: Box :: 
  { TwoStateAt.Cell.Plus#requires(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.TwoStateAt.Cell())
       && $IsAlloc(this, Tclass.TwoStateAt.Cell(), $prevHeap)
       && $IsBox(y#0, TwoStateAt.Cell.Plus$Y)
     ==> TwoStateAt.Cell.Plus#requires(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0)
       == $IsAllocBox(y#0, TwoStateAt.Cell.Plus$Y, $prevHeap));

// definition axiom for TwoStateAt.Cell.Plus (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall TwoStateAt.Cell.Plus$Y: Ty, $prevHeap: Heap, $Heap: Heap, this: ref, y#0: Box :: 
    { TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0), $IsGoodHeap($Heap) } 
    TwoStateAt.Cell.Plus#canCall(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.TwoStateAt.Cell())
           && $IsAlloc(this, Tclass.TwoStateAt.Cell(), $prevHeap)
           && $IsBox(y#0, TwoStateAt.Cell.Plus$Y))
       ==> TwoStateAt.__default.SP#canCall(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0)
         && TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0)
           == TwoStateAt.__default.SP(TwoStateAt.Cell.Plus$Y, $prevHeap, $Heap, this, y#0));

procedure CheckWellformed$$TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass.TwoStateAt.Cell())
         && $IsAlloc(this, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.Plus$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.Plus$Y, previous$Heap));
  free requires 2 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: ref, 
    y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: ref;
  var ##y#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Plus
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(256,22): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        ##c#0 := this;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#0 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#0, TwoStateAt.Cell.Plus$Y, $Heap);
        assert $IsAlloc(this, Tclass.TwoStateAt.Cell(), old($Heap));
        assert $IsAllocBox(y#0, TwoStateAt.Cell.Plus$Y, old($Heap));
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == ##c#0 ==> $_Frame[$o, $f]);
        assume TwoStateAt.__default.SP#canCall(TwoStateAt.Cell.Plus$Y, old($Heap), $Heap, this, y#0);
        assume TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, old($Heap), $Heap, this, y#0)
           == TwoStateAt.__default.SP(TwoStateAt.Cell.Plus$Y, old($Heap), $Heap, this, y#0);
        assume TwoStateAt.__default.SP#canCall(TwoStateAt.Cell.Plus$Y, old($Heap), $Heap, this, y#0);
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, old($Heap), $Heap, this, y#0), TInt);
        assert b$reqreads#0;
    }
}



procedure {:_induction this} CheckWellformed$$TwoStateAt.Cell.LL(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.LL$Y: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass.TwoStateAt.Cell())
         && $IsAlloc(this, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.LL$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.LL$Y, previous$Heap));
  free requires 21 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.Cell.LL$Y, previous$Heap);
  modifies $Heap, $Tick;



implementation {:_induction this} CheckWellformed$$TwoStateAt.Cell.LL(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.LL$Y: Ty, 
    this: ref, 
    y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: LL, CheckWellformed$$TwoStateAt.Cell.LL
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(262,19): initial state"} true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(263,24): post-state"} true;
    assert $IsAlloc(this, Tclass.TwoStateAt.Cell(), old($Heap));
    assume read(old($Heap), this, TwoStateAt.Cell.data)
       < read($Heap, this, TwoStateAt.Cell.data);
}



procedure {:_induction this} Call$$TwoStateAt.Cell.LL(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.LL$Y: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass.TwoStateAt.Cell())
         && $IsAlloc(this, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.LL$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.LL$Y, previous$Heap));
  requires $IsAllocBox(y#0, TwoStateAt.Cell.LL$Y, previous$Heap);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read(previous$Heap, this, TwoStateAt.Cell.data)
     < read(current$Heap, this, TwoStateAt.Cell.data);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this} Impl$$TwoStateAt.Cell.LL(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.LL$Y: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass.TwoStateAt.Cell())
         && $IsAlloc(this, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.LL$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.LL$Y, previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.Cell.LL$Y, previous$Heap);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read(previous$Heap, this, TwoStateAt.Cell.data)
     < read(current$Heap, this, TwoStateAt.Cell.data);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction this} Impl$$TwoStateAt.Cell.LL(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.LL$Y: Ty, 
    this: ref, 
    y#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var c##1_0: ref;
  var y##1_0: Box;

    // AddMethodImpl: LL, Impl$$TwoStateAt.Cell.LL
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(264,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref :: 
      $Is($ih#this0#0, Tclass.TwoStateAt.Cell()) && Lit(true) && false
         ==> read($initHeapForallStmt#0, this, TwoStateAt.Cell.data)
           < read($Heap, this, TwoStateAt.Cell.data));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(265,7)
    assert $IsAlloc(this, Tclass.TwoStateAt.Cell(), old($Heap));
    assume true;
    if (read(old($Heap), this, TwoStateAt.Cell.data)
       < read($Heap, this, TwoStateAt.Cell.data))
    {
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(267,14)
        assert $IsAlloc(this, Tclass.TwoStateAt.Cell(), old($Heap));
        assume true;
        if (read(old($Heap), this, TwoStateAt.Cell.data)
           != read($Heap, this, TwoStateAt.Cell.data))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(269,22)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_0 := this;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_0 := y#0;
            assert $IsAlloc(this, Tclass.TwoStateAt.Cell(), old($Heap));
            assert $IsAllocBox(y#0, TwoStateAt.Cell.LL$Y, old($Heap));
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$TwoStateAt.Cell.IdentityLemma(old($Heap), $Heap, TwoStateAt.Cell.LL$Y, c##1_0, y##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(269,30)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(270,9)
            assume true;
            assert false;
        }
        else
        {
        }
    }
}



procedure CheckWellformed$$TwoStateAt.Cell.IdentityLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.IdentityLemma$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.IdentityLemma$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.IdentityLemma$Y, previous$Heap));
  free requires 4 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.Cell.IdentityLemma$Y, previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.Cell.IdentityLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.IdentityLemma$Y: Ty, 
    c#0: ref, 
    y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: IdentityLemma, CheckWellformed$$TwoStateAt.Cell.IdentityLemma
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(275,26): initial state"} true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(276,26): post-state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert c#0 != null;
    assume read(old($Heap), c#0, TwoStateAt.Cell.data)
       == read($Heap, c#0, TwoStateAt.Cell.data);
}



procedure Call$$TwoStateAt.Cell.IdentityLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.IdentityLemma$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.IdentityLemma$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.IdentityLemma$Y, previous$Heap));
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.Cell.IdentityLemma$Y, previous$Heap);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read(previous$Heap, c#0, TwoStateAt.Cell.data)
     == read(current$Heap, c#0, TwoStateAt.Cell.data);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.Cell.IdentityLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.IdentityLemma$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.Cell.IdentityLemma$Y)
         && $IsAllocBox(y#0, TwoStateAt.Cell.IdentityLemma$Y, previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.Cell.IdentityLemma$Y, previous$Heap);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read(previous$Heap, c#0, TwoStateAt.Cell.data)
     == read(current$Heap, c#0, TwoStateAt.Cell.data);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.Cell.IdentityLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.Cell.IdentityLemma$Y: Ty, 
    c#0: ref, 
    y#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: IdentityLemma, Impl$$TwoStateAt.Cell.IdentityLemma
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(277,4): initial state"} true;
    $_reverifyPost := false;
}



// TwoStateAt.Cell: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.TwoStateAt.Cell()) } 
  $Is(c#0, Tclass.TwoStateAt.Cell())
     <==> $Is(c#0, Tclass.TwoStateAt.Cell?()) && c#0 != null);

// TwoStateAt.Cell: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $h) } 
  $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $h)
     <==> $IsAlloc(c#0, Tclass.TwoStateAt.Cell?(), $h));

// Constructor function declaration
function #TwoStateAt.DT.Green() : DatatypeType;

const unique ##TwoStateAt.DT.Green: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#TwoStateAt.DT.Green()) == ##TwoStateAt.DT.Green;

function TwoStateAt.DT.Green_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TwoStateAt.DT.Green_q(d) } 
  TwoStateAt.DT.Green_q(d) <==> DatatypeCtorId(d) == ##TwoStateAt.DT.Green);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TwoStateAt.DT.Green_q(d) } 
  TwoStateAt.DT.Green_q(d) ==> d == #TwoStateAt.DT.Green());

function Tclass.TwoStateAt.DT(Ty) : Ty;

const unique Tagclass.TwoStateAt.DT: TyTag;

// Tclass.TwoStateAt.DT Tag
axiom (forall TwoStateAt.DT$X: Ty :: 
  { Tclass.TwoStateAt.DT(TwoStateAt.DT$X) } 
  Tag(Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) == Tagclass.TwoStateAt.DT
     && TagFamily(Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) == tytagFamily$DT);

// Tclass.TwoStateAt.DT injectivity 0
axiom (forall TwoStateAt.DT$X: Ty :: 
  { Tclass.TwoStateAt.DT(TwoStateAt.DT$X) } 
  Tclass.TwoStateAt.DT_0(Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) == TwoStateAt.DT$X);

function Tclass.TwoStateAt.DT_0(Ty) : Ty;

// Box/unbox axiom for Tclass.TwoStateAt.DT
axiom (forall TwoStateAt.DT$X: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) } 
  $IsBox(bx, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.TwoStateAt.DT(TwoStateAt.DT$X)));

// Constructor $Is
axiom (forall TwoStateAt.DT$X: Ty :: 
  { $Is(#TwoStateAt.DT.Green(), Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) } 
  $Is(#TwoStateAt.DT.Green(), Tclass.TwoStateAt.DT(TwoStateAt.DT$X)));

// Constructor $IsAlloc
axiom (forall TwoStateAt.DT$X: Ty, $h: Heap :: 
  { $IsAlloc(#TwoStateAt.DT.Green(), Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#TwoStateAt.DT.Green(), Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $h));

// Constructor literal
axiom #TwoStateAt.DT.Green() == Lit(#TwoStateAt.DT.Green());

// Constructor function declaration
function #TwoStateAt.DT.Blue(Box) : DatatypeType;

const unique ##TwoStateAt.DT.Blue: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box :: 
  { #TwoStateAt.DT.Blue(a#5#0#0) } 
  DatatypeCtorId(#TwoStateAt.DT.Blue(a#5#0#0)) == ##TwoStateAt.DT.Blue);

function TwoStateAt.DT.Blue_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TwoStateAt.DT.Blue_q(d) } 
  TwoStateAt.DT.Blue_q(d) <==> DatatypeCtorId(d) == ##TwoStateAt.DT.Blue);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TwoStateAt.DT.Blue_q(d) } 
  TwoStateAt.DT.Blue_q(d)
     ==> (exists a#6#0#0: Box :: d == #TwoStateAt.DT.Blue(a#6#0#0)));

// Constructor $Is
axiom (forall TwoStateAt.DT$X: Ty, a#7#0#0: Box :: 
  { $Is(#TwoStateAt.DT.Blue(a#7#0#0), Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) } 
  $Is(#TwoStateAt.DT.Blue(a#7#0#0), Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
     <==> $IsBox(a#7#0#0, TwoStateAt.DT$X));

// Constructor $IsAlloc
axiom (forall TwoStateAt.DT$X: Ty, a#8#0#0: Box, $h: Heap :: 
  { $IsAlloc(#TwoStateAt.DT.Blue(a#8#0#0), Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TwoStateAt.DT.Blue(a#8#0#0), Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $h)
       <==> $IsAllocBox(a#8#0#0, TwoStateAt.DT$X, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, TwoStateAt.DT$X: Ty, $h: Heap :: 
  { $IsAllocBox(TwoStateAt.DT.value(d), TwoStateAt.DT$X, $h) } 
  $IsGoodHeap($h)
       && 
      TwoStateAt.DT.Blue_q(d)
       && $IsAlloc(d, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $h)
     ==> $IsAllocBox(TwoStateAt.DT.value(d), TwoStateAt.DT$X, $h));

// Constructor literal
axiom (forall a#9#0#0: Box :: 
  { #TwoStateAt.DT.Blue(Lit(a#9#0#0)) } 
  #TwoStateAt.DT.Blue(Lit(a#9#0#0)) == Lit(#TwoStateAt.DT.Blue(a#9#0#0)));

function TwoStateAt.DT.value(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box :: 
  { #TwoStateAt.DT.Blue(a#10#0#0) } 
  TwoStateAt.DT.value(#TwoStateAt.DT.Blue(a#10#0#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box :: 
  { #TwoStateAt.DT.Blue(a#11#0#0) } 
  BoxRank(a#11#0#0) < DtRank(#TwoStateAt.DT.Blue(a#11#0#0)));

// Depth-one case-split function
function $IsA#TwoStateAt.DT(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#TwoStateAt.DT(d) } 
  $IsA#TwoStateAt.DT(d) ==> TwoStateAt.DT.Green_q(d) || TwoStateAt.DT.Blue_q(d));

// Questionmark data type disjunctivity
axiom (forall TwoStateAt.DT$X: Ty, d: DatatypeType :: 
  { TwoStateAt.DT.Blue_q(d), $Is(d, Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) } 
    { TwoStateAt.DT.Green_q(d), $Is(d, Tclass.TwoStateAt.DT(TwoStateAt.DT$X)) } 
  $Is(d, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
     ==> TwoStateAt.DT.Green_q(d) || TwoStateAt.DT.Blue_q(d));

// Datatype extensional equality declaration
function TwoStateAt.DT#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #TwoStateAt.DT.Green
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TwoStateAt.DT#Equal(a, b), TwoStateAt.DT.Green_q(a) } 
    { TwoStateAt.DT#Equal(a, b), TwoStateAt.DT.Green_q(b) } 
  TwoStateAt.DT.Green_q(a) && TwoStateAt.DT.Green_q(b)
     ==> (TwoStateAt.DT#Equal(a, b) <==> true));

// Datatype extensional equality definition: #TwoStateAt.DT.Blue
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TwoStateAt.DT#Equal(a, b), TwoStateAt.DT.Blue_q(a) } 
    { TwoStateAt.DT#Equal(a, b), TwoStateAt.DT.Blue_q(b) } 
  TwoStateAt.DT.Blue_q(a) && TwoStateAt.DT.Blue_q(b)
     ==> (TwoStateAt.DT#Equal(a, b)
       <==> TwoStateAt.DT.value(a) == TwoStateAt.DT.value(b)));

// Datatype extensionality axiom: TwoStateAt.DT
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TwoStateAt.DT#Equal(a, b) } 
  TwoStateAt.DT#Equal(a, b) <==> a == b);

const unique class.TwoStateAt.DT: ClassName;

function {:inline} TwoStateAt.DT.sc(TwoStateAt.DT$X: Ty) : int
{
  LitInt(18)
}

procedure CheckWellformed$$TwoStateAt.DT.sc(TwoStateAt.DT$X: Ty);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap;



// DT.sc: Type axiom
axiom 41 < $FunctionContextHeight
   ==> (forall TwoStateAt.DT$X: Ty :: 
    { TwoStateAt.DT.sc(TwoStateAt.DT$X) } 
    $Is(TwoStateAt.DT.sc(TwoStateAt.DT$X), TInt));

// DT.sc: Allocation axiom
axiom 41 < $FunctionContextHeight
   ==> (forall TwoStateAt.DT$X: Ty, $h: Heap :: 
    { $IsAlloc(TwoStateAt.DT.sc(TwoStateAt.DT$X), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(TwoStateAt.DT.sc(TwoStateAt.DT$X), TInt, $h));

// function declaration for TwoStateAt.DT.F
function TwoStateAt.DT.F(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    this: DatatypeType, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : int;

function TwoStateAt.DT.F#canCall(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    this: DatatypeType, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : bool;

// frame axiom for TwoStateAt.DT.F
axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    this: DatatypeType, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $h1, this, x#0, y#0, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
       && (TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $h0, this, x#0, y#0, c#0)
         || (
          $IsBox(x#0, TwoStateAt.DT$X)
           && $IsBox(y#0, TwoStateAt.DT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $h0, this, x#0, y#0, c#0)
       == TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $h1, this, x#0, y#0, c#0));

// consequence axiom for TwoStateAt.DT.F
axiom 5 <= $FunctionContextHeight
   ==> (forall TwoStateAt.DT$X: Ty, 
      TwoStateAt.DT.F$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      this: DatatypeType, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0) } 
    TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
           && $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $prevHeap)
           && $IsBox(x#0, TwoStateAt.DT$X)
           && $IsBox(y#0, TwoStateAt.DT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.DT.F#requires(Ty, Ty, Heap, Heap, DatatypeType, Box, Box, ref) : bool;

// #requires axiom for TwoStateAt.DT.F
axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $Heap: Heap, 
    this: DatatypeType, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { TwoStateAt.DT.F#requires(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && 
      $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
       && $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $prevHeap)
       && $IsBox(x#0, TwoStateAt.DT$X)
       && $IsBox(y#0, TwoStateAt.DT.F$Y)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.DT.F#requires(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
       == (
        $IsAllocBox(x#0, TwoStateAt.DT$X, $prevHeap)
         && $IsAllocBox(y#0, TwoStateAt.DT.F$Y, $prevHeap)
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)));

// definition axiom for TwoStateAt.DT.F (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall TwoStateAt.DT$X: Ty, 
      TwoStateAt.DT.F$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      this: DatatypeType, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
    TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
           && $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), $prevHeap)
           && $IsBox(x#0, TwoStateAt.DT$X)
           && $IsBox(y#0, TwoStateAt.DT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
         == read($Heap, c#0, TwoStateAt.Cell.data)
           - read($prevHeap, c#0, TwoStateAt.Cell.data));

procedure CheckWellformed$$TwoStateAt.DT.F(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: DatatypeType
       where $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.F$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.F$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap));
  free requires 5 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.DT.F(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: DatatypeType, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(479,22): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assert c#0 != null;
        b$reqreads#0 := $_Frame[c#0, TwoStateAt.Cell.data];
        assert c#0 != null;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, old($Heap), $Heap, this, x#0, y#0, c#0)
           == read($Heap, c#0, TwoStateAt.Cell.data)
             - read(old($Heap), c#0, TwoStateAt.Cell.data);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, old($Heap), $Heap, this, x#0, y#0, c#0), 
          TInt);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$TwoStateAt.DT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.L$Y: Ty, 
    this: DatatypeType
       where $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  free requires 7 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.DT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.DT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.L$Y: Ty, 
    this: DatatypeType, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: L, CheckWellformed$$TwoStateAt.DT.L
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(484,19): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert c#0 != null;
    assume read(old($Heap), c#0, TwoStateAt.Cell.data)
       <= read($Heap, c#0, TwoStateAt.Cell.data);
    havoc n#0;
}



procedure Call$$TwoStateAt.DT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.L$Y: Ty, 
    this: DatatypeType
       where $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  requires $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.DT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.DT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.L$Y: Ty, 
    this: DatatypeType
       where $Is(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0, $_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.DT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.DT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.L$Y: Ty, 
    this: DatatypeType, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: Box;
  var ##y#0: Box;
  var ##c#0: ref;

    // AddMethodImpl: L, Impl$$TwoStateAt.DT.L
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(486,4): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(487,9)
    assume true;
    ##x#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#0, TwoStateAt.DT$X, $Heap);
    ##y#0 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#0, TwoStateAt.DT.L$Y, $Heap);
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
    assert $IsAlloc(this, Tclass.TwoStateAt.DT(TwoStateAt.DT$X), old($Heap));
    assert $IsAllocBox(x#0, TwoStateAt.DT$X, old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt.DT.L$Y, old($Heap));
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assume TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, TwoStateAt.DT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0);
    assume TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, TwoStateAt.DT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0);
    assert $Is(TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0), 
      Tclass._System.nat());
    n#0 := TwoStateAt.DT.F(TwoStateAt.DT$X, TwoStateAt.DT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(487,21)"} true;
}



// function declaration for TwoStateAt.DT.G
function TwoStateAt.DT.G(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : int;

function TwoStateAt.DT.G#canCall(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : bool;

// frame axiom for TwoStateAt.DT.G
axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $h1, x#0, y#0, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.DT.G#canCall(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $h0, x#0, y#0, c#0)
         || (
          $IsBox(x#0, TwoStateAt.DT$X)
           && $IsBox(y#0, TwoStateAt.DT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $h0, x#0, y#0, c#0)
       == TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $h1, x#0, y#0, c#0));

// consequence axiom for TwoStateAt.DT.G
axiom 8 <= $FunctionContextHeight
   ==> (forall TwoStateAt.DT$X: Ty, 
      TwoStateAt.DT.G$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $Heap, x#0, y#0, c#0) } 
    TwoStateAt.DT.G#canCall(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $Heap, x#0, y#0, c#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $IsBox(x#0, TwoStateAt.DT$X)
           && $IsBox(y#0, TwoStateAt.DT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.DT.G#requires(Ty, Ty, Heap, Heap, Box, Box, ref) : bool;

// #requires axiom for TwoStateAt.DT.G
axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $Heap: Heap, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { TwoStateAt.DT.G#requires(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $Heap, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $IsBox(x#0, TwoStateAt.DT$X)
       && $IsBox(y#0, TwoStateAt.DT.G$Y)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.DT.G#requires(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $Heap, x#0, y#0, c#0)
       == (
        $IsAllocBox(x#0, TwoStateAt.DT$X, $prevHeap)
         && $IsAllocBox(y#0, TwoStateAt.DT.G$Y, $prevHeap)
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)));

// definition axiom for TwoStateAt.DT.G (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall TwoStateAt.DT$X: Ty, 
      TwoStateAt.DT.G$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $Heap, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
    TwoStateAt.DT.G#canCall(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $Heap, x#0, y#0, c#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $IsBox(x#0, TwoStateAt.DT$X)
           && $IsBox(y#0, TwoStateAt.DT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, 
          TwoStateAt.DT.G$Y, 
          $prevHeap, 
          $Heap, 
          Lit(#TwoStateAt.DT.Green()), 
          x#0, 
          y#0, 
          c#0)
         && TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap, $Heap, x#0, y#0, c#0)
           == TwoStateAt.DT.F(TwoStateAt.DT$X, 
            TwoStateAt.DT.G$Y, 
            $prevHeap, 
            $Heap, 
            Lit(#TwoStateAt.DT.Green()), 
            x#0, 
            y#0, 
            c#0));

procedure CheckWellformed$$TwoStateAt.DT.G(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.G$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.G$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap));
  free requires 8 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.DT.G(TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: Box;
  var ##y#0: Box;
  var ##c#0: ref;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function G
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(489,29): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, TwoStateAt.DT$X, $Heap);
        ##y#0 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#0, TwoStateAt.DT.G$Y, $Heap);
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(Lit(#TwoStateAt.DT.Green()), Tclass.TwoStateAt.DT(TwoStateAt.DT$X), old($Heap));
        assert $IsAllocBox(x#0, TwoStateAt.DT$X, old($Heap));
        assert $IsAllocBox(y#0, TwoStateAt.DT.G$Y, old($Heap));
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == ##c#0 ==> $_Frame[$o, $f]);
        assume TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, 
          TwoStateAt.DT.G$Y, 
          old($Heap), 
          $Heap, 
          Lit(#TwoStateAt.DT.Green()), 
          x#0, 
          y#0, 
          c#0);
        assume TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, old($Heap), $Heap, x#0, y#0, c#0)
           == TwoStateAt.DT.F(TwoStateAt.DT$X, 
            TwoStateAt.DT.G$Y, 
            old($Heap), 
            $Heap, 
            Lit(#TwoStateAt.DT.Green()), 
            x#0, 
            y#0, 
            c#0);
        assume TwoStateAt.DT.F#canCall(TwoStateAt.DT$X, 
          TwoStateAt.DT.G$Y, 
          old($Heap), 
          $Heap, 
          Lit(#TwoStateAt.DT.Green()), 
          x#0, 
          y#0, 
          c#0);
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.DT.G(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, old($Heap), $Heap, x#0, y#0, c#0), 
          TInt);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$TwoStateAt.DT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.M$Y: Ty, 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  free requires 9 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.DT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.DT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.M$Y: Ty, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, CheckWellformed$$TwoStateAt.DT.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(494,26): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert c#0 != null;
    assume read(old($Heap), c#0, TwoStateAt.Cell.data)
       <= read($Heap, c#0, TwoStateAt.Cell.data);
    havoc n#0;
}



procedure Call$$TwoStateAt.DT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.M$Y: Ty, 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  requires $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.DT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.DT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.M$Y: Ty, 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.DT$X) && $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.DT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.DT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0, $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.DT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.DT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.DT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.M$Y: Ty, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int where LitInt(0) <= $rhs##0;
  var x##0: Box;
  var y##0: Box;
  var c##0: ref;

    // AddMethodImpl: M, Impl$$TwoStateAt.DT.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(496,4): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(497,19)
    assume true;
    // TrCallStmt: Adding lhs with type nat
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := x#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := y#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assert $IsAlloc(Lit(#TwoStateAt.DT.Green()), Tclass.TwoStateAt.DT(TwoStateAt.DT$X), old($Heap));
    assert $IsAllocBox(x#0, TwoStateAt.DT$X, old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt.DT.M$Y, old($Heap));
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$TwoStateAt.DT.L(old($Heap), $Heap, TwoStateAt.DT$X, TwoStateAt.DT.M$Y, Lit(#TwoStateAt.DT.Green()), x##0, y##0, c##0);
    // TrCallStmt: After ProcessCallStmt
    n#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(497,27)"} true;
}



procedure CheckWellformed$$TwoStateAt.NT(x#0: int);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.NT(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype NT
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(501,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(0) <= x#0)
        {
        }

        assume LitInt(0) <= x#0 && x#0 < 86;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(0) <= LitInt(0);
        assert {:subsumption 0} 0 < 86;
    }
}



function Tclass.TwoStateAt.NT() : Ty;

const unique Tagclass.TwoStateAt.NT: TyTag;

// Tclass.TwoStateAt.NT Tag
axiom Tag(Tclass.TwoStateAt.NT()) == Tagclass.TwoStateAt.NT
   && TagFamily(Tclass.TwoStateAt.NT()) == tytagFamily$NT;

// Box/unbox axiom for Tclass.TwoStateAt.NT
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TwoStateAt.NT()) } 
  $IsBox(bx, Tclass.TwoStateAt.NT())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass.TwoStateAt.NT()));

// TwoStateAt.NT: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass.TwoStateAt.NT()) } 
  $Is(x#0, Tclass.TwoStateAt.NT()) <==> LitInt(0) <= x#0 && x#0 < 86);

// TwoStateAt.NT: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass.TwoStateAt.NT(), $h) } 
  $IsAlloc(x#0, Tclass.TwoStateAt.NT(), $h));

const unique class.TwoStateAt.NT: ClassName;

function {:inline} TwoStateAt.NT.value(this: int) : int
{
  LitInt(18)
}

procedure CheckWellformed$$TwoStateAt.NT.value(this: int where LitInt(0) <= this && this < 86);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap;



// NT.value: Type axiom
axiom 39 < $FunctionContextHeight
   ==> (forall $o: int :: 
    { TwoStateAt.NT.value($o) } 
    $Is(TwoStateAt.NT.value($o), TInt));

// NT.value: Allocation axiom
axiom 39 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: int :: 
    { TwoStateAt.NT.value($o), $IsAlloc($o, Tclass.TwoStateAt.NT(), $h) } 
    $IsGoodHeap($h) && $IsAlloc($o, Tclass.TwoStateAt.NT(), $h)
       ==> $IsAlloc(TwoStateAt.NT.value($o), TInt, $h));

function {:inline} TwoStateAt.NT.sc() : int
{
  LitInt(18)
}

procedure CheckWellformed$$TwoStateAt.NT.sc();
  free requires 42 == $FunctionContextHeight;
  modifies $Heap;



// NT.sc: Type axiom
axiom 42 < $FunctionContextHeight ==> $Is(TwoStateAt.NT.sc(), TInt);

// NT.sc: Allocation axiom
axiom 42 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(TwoStateAt.NT.sc(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(TwoStateAt.NT.sc(), TInt, $h));

// function declaration for TwoStateAt.NT.F
function TwoStateAt.NT.F(TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    this: int, 
    y#0: Box, 
    c#0: ref)
   : int;

function TwoStateAt.NT.F#canCall(TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    this: int, 
    y#0: Box, 
    c#0: ref)
   : bool;

// frame axiom for TwoStateAt.NT.F
axiom (forall TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    this: int, 
    y#0: Box, 
    c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $h1, this, y#0, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      LitInt(0) <= this
       && this < 86
       && (TwoStateAt.NT.F#canCall(TwoStateAt.NT.F$Y, $prevHeap, $h0, this, y#0, c#0)
         || ($IsBox(y#0, TwoStateAt.NT.F$Y) && $Is(c#0, Tclass.TwoStateAt.Cell())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $h0, this, y#0, c#0)
       == TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $h1, this, y#0, c#0));

// consequence axiom for TwoStateAt.NT.F
axiom 10 <= $FunctionContextHeight
   ==> (forall TwoStateAt.NT.F$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      this: int, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $Heap, this, y#0, c#0) } 
    TwoStateAt.NT.F#canCall(TwoStateAt.NT.F$Y, $prevHeap, $Heap, this, y#0, c#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          LitInt(0) <= this
           && this < 86
           && $IsBox(y#0, TwoStateAt.NT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.NT.F#requires(Ty, Heap, Heap, int, Box, ref) : bool;

// #requires axiom for TwoStateAt.NT.F
axiom (forall TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $Heap: Heap, 
    this: int, 
    y#0: Box, 
    c#0: ref :: 
  { TwoStateAt.NT.F#requires(TwoStateAt.NT.F$Y, $prevHeap, $Heap, this, y#0, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && 
      LitInt(0) <= this
       && this < 86
       && $IsBox(y#0, TwoStateAt.NT.F$Y)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.NT.F#requires(TwoStateAt.NT.F$Y, $prevHeap, $Heap, this, y#0, c#0)
       == ($IsAllocBox(y#0, TwoStateAt.NT.F$Y, $prevHeap)
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)));

// definition axiom for TwoStateAt.NT.F (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall TwoStateAt.NT.F$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      this: int, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $Heap, this, y#0, c#0), $IsGoodHeap($Heap) } 
    TwoStateAt.NT.F#canCall(TwoStateAt.NT.F$Y, $prevHeap, $Heap, this, y#0, c#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          LitInt(0) <= this
           && this < 86
           && $IsBox(y#0, TwoStateAt.NT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $Heap, this, y#0, c#0)
         == read($Heap, c#0, TwoStateAt.Cell.data)
           - read($prevHeap, c#0, TwoStateAt.Cell.data));

procedure CheckWellformed$$TwoStateAt.NT.F(TwoStateAt.NT.F$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: int where LitInt(0) <= this && this < 86, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.F$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.F$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap));
  free requires 10 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.NT.F(TwoStateAt.NT.F$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: int, 
    y#0: Box, 
    c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(504,22): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assert c#0 != null;
        b$reqreads#0 := $_Frame[c#0, TwoStateAt.Cell.data];
        assert c#0 != null;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.NT.F(TwoStateAt.NT.F$Y, old($Heap), $Heap, this, y#0, c#0)
           == read($Heap, c#0, TwoStateAt.Cell.data)
             - read(old($Heap), c#0, TwoStateAt.Cell.data);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.NT.F(TwoStateAt.NT.F$Y, old($Heap), $Heap, this, y#0, c#0), TInt);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$TwoStateAt.NT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.L$Y: Ty, 
    this: int where LitInt(0) <= this && this < 86, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  free requires 11 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.NT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.NT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.L$Y: Ty, 
    this: int, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: L, CheckWellformed$$TwoStateAt.NT.L
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(509,19): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert c#0 != null;
    assume read(old($Heap), c#0, TwoStateAt.Cell.data)
       <= read($Heap, c#0, TwoStateAt.Cell.data);
    havoc n#0;
}



procedure Call$$TwoStateAt.NT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.L$Y: Ty, 
    this: int where LitInt(0) <= this && this < 86, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  requires $IsAllocBox(y#0, TwoStateAt.NT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.NT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.L$Y: Ty, 
    this: int where LitInt(0) <= this && this < 86, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0, $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.NT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.NT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.L$Y: Ty, 
    this: int, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##y#0: Box;
  var ##c#0: ref;

    // AddMethodImpl: L, Impl$$TwoStateAt.NT.L
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(511,4): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(512,9)
    assume true;
    ##y#0 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#0, TwoStateAt.NT.L$Y, $Heap);
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
    assert $IsAllocBox(y#0, TwoStateAt.NT.L$Y, old($Heap));
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assume TwoStateAt.NT.F#canCall(TwoStateAt.NT.L$Y, old($Heap), $Heap, this, y#0, c#0);
    assume TwoStateAt.NT.F#canCall(TwoStateAt.NT.L$Y, old($Heap), $Heap, this, y#0, c#0);
    assert $Is(TwoStateAt.NT.F(TwoStateAt.NT.L$Y, old($Heap), $Heap, this, y#0, c#0), 
      Tclass._System.nat());
    n#0 := TwoStateAt.NT.F(TwoStateAt.NT.L$Y, old($Heap), $Heap, this, y#0, c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(512,18)"} true;
}



// function declaration for TwoStateAt.NT.G
function TwoStateAt.NT.G(TwoStateAt.NT.G$Y: Ty, $prevHeap: Heap, $heap: Heap, y#0: Box, c#0: ref) : int;

function TwoStateAt.NT.G#canCall(TwoStateAt.NT.G$Y: Ty, $prevHeap: Heap, $heap: Heap, y#0: Box, c#0: ref) : bool;

// frame axiom for TwoStateAt.NT.G
axiom (forall TwoStateAt.NT.G$Y: Ty, $prevHeap: Heap, $h0: Heap, $h1: Heap, y#0: Box, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $h1, y#0, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.NT.G#canCall(TwoStateAt.NT.G$Y, $prevHeap, $h0, y#0, c#0)
         || ($IsBox(y#0, TwoStateAt.NT.G$Y) && $Is(c#0, Tclass.TwoStateAt.Cell())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $h0, y#0, c#0)
       == TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $h1, y#0, c#0));

// consequence axiom for TwoStateAt.NT.G
axiom 13 <= $FunctionContextHeight
   ==> (forall TwoStateAt.NT.G$Y: Ty, $prevHeap: Heap, $Heap: Heap, y#0: Box, c#0: ref :: 
    { TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $Heap, y#0, c#0) } 
    TwoStateAt.NT.G#canCall(TwoStateAt.NT.G$Y, $prevHeap, $Heap, y#0, c#0)
         || (13 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $IsBox(y#0, TwoStateAt.NT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.NT.G#requires(Ty, Heap, Heap, Box, ref) : bool;

// #requires axiom for TwoStateAt.NT.G
axiom (forall TwoStateAt.NT.G$Y: Ty, $prevHeap: Heap, $Heap: Heap, y#0: Box, c#0: ref :: 
  { TwoStateAt.NT.G#requires(TwoStateAt.NT.G$Y, $prevHeap, $Heap, y#0, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $IsBox(y#0, TwoStateAt.NT.G$Y)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.NT.G#requires(TwoStateAt.NT.G$Y, $prevHeap, $Heap, y#0, c#0)
       == ($IsAllocBox(y#0, TwoStateAt.NT.G$Y, $prevHeap)
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)));

// definition axiom for TwoStateAt.NT.G (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall TwoStateAt.NT.G$Y: Ty, $prevHeap: Heap, $Heap: Heap, y#0: Box, c#0: ref :: 
    { TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $Heap, y#0, c#0), $IsGoodHeap($Heap) } 
    TwoStateAt.NT.G#canCall(TwoStateAt.NT.G$Y, $prevHeap, $Heap, y#0, c#0)
         || (13 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $IsBox(y#0, TwoStateAt.NT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.NT.F#canCall(TwoStateAt.NT.G$Y, $prevHeap, $Heap, LitInt(82), y#0, c#0)
         && TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $Heap, y#0, c#0)
           == TwoStateAt.NT.F(TwoStateAt.NT.G$Y, $prevHeap, $Heap, LitInt(82), y#0, c#0));

procedure CheckWellformed$$TwoStateAt.NT.G(TwoStateAt.NT.G$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.G$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.G$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap));
  free requires 13 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.NT.G(TwoStateAt.NT.G$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    y#0: Box, 
    c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var ##y#0: Box;
  var ##c#0: ref;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function G
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(514,29): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        newtype$check#0 := LitInt(82);
        assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 86;
        ##y#0 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#0, TwoStateAt.NT.G$Y, $Heap);
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAllocBox(y#0, TwoStateAt.NT.G$Y, old($Heap));
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == ##c#0 ==> $_Frame[$o, $f]);
        assume TwoStateAt.NT.F#canCall(TwoStateAt.NT.G$Y, old($Heap), $Heap, LitInt(82), y#0, c#0);
        assume TwoStateAt.NT.G(TwoStateAt.NT.G$Y, old($Heap), $Heap, y#0, c#0)
           == TwoStateAt.NT.F(TwoStateAt.NT.G$Y, old($Heap), $Heap, LitInt(82), y#0, c#0);
        assume TwoStateAt.NT.F#canCall(TwoStateAt.NT.G$Y, old($Heap), $Heap, LitInt(82), y#0, c#0);
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.NT.G(TwoStateAt.NT.G$Y, old($Heap), $Heap, y#0, c#0), TInt);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$TwoStateAt.NT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.M$Y: Ty, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  free requires 14 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.NT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.NT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.M$Y: Ty, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, CheckWellformed$$TwoStateAt.NT.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(519,26): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert c#0 != null;
    assume read(old($Heap), c#0, TwoStateAt.Cell.data)
       <= read($Heap, c#0, TwoStateAt.Cell.data);
    havoc n#0;
}



procedure Call$$TwoStateAt.NT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.M$Y: Ty, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  requires $IsAllocBox(y#0, TwoStateAt.NT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.NT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.M$Y: Ty, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.NT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.NT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0, $_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.NT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.NT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.NT.M$Y: Ty, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int where LitInt(0) <= $rhs##0;
  var newtype$check#0: int;
  var y##0: Box;
  var c##0: ref;

    // AddMethodImpl: M, Impl$$TwoStateAt.NT.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(521,4): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(522,24)
    assume true;
    // TrCallStmt: Adding lhs with type nat
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#0 := LitInt(82);
    assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 86;
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := y#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assert $IsAllocBox(y#0, TwoStateAt.NT.M$Y, old($Heap));
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$TwoStateAt.NT.L(old($Heap), $Heap, TwoStateAt.NT.M$Y, LitInt(82), y##0, c##0);
    // TrCallStmt: After ProcessCallStmt
    n#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(522,29)"} true;
}



function #$OT(Ty) : Ty;

const unique class.TwoStateAt.OT: ClassName;

function {:inline} TwoStateAt.OT.value(TwoStateAt.OT$X: Ty, this: Box) : int
{
  LitInt(18)
}

function Tclass.TwoStateAt.OT(Ty) : Ty;

const unique Tagclass.TwoStateAt.OT: TyTag;

// Tclass.TwoStateAt.OT Tag
axiom (forall TwoStateAt.OT$X: Ty :: 
  { Tclass.TwoStateAt.OT(TwoStateAt.OT$X) } 
  Tag(Tclass.TwoStateAt.OT(TwoStateAt.OT$X)) == Tagclass.TwoStateAt.OT
     && TagFamily(Tclass.TwoStateAt.OT(TwoStateAt.OT$X)) == tytagFamily$OT);

// Tclass.TwoStateAt.OT injectivity 0
axiom (forall TwoStateAt.OT$X: Ty :: 
  { Tclass.TwoStateAt.OT(TwoStateAt.OT$X) } 
  Tclass.TwoStateAt.OT_0(Tclass.TwoStateAt.OT(TwoStateAt.OT$X)) == TwoStateAt.OT$X);

function Tclass.TwoStateAt.OT_0(Ty) : Ty;

// Box/unbox axiom for Tclass.TwoStateAt.OT
axiom (forall TwoStateAt.OT$X: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.TwoStateAt.OT(TwoStateAt.OT$X)) } 
  $IsBox(bx, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
     ==> $Box($Unbox(bx): Box) == bx
       && $Is($Unbox(bx): Box, Tclass.TwoStateAt.OT(TwoStateAt.OT$X)));

procedure CheckWellformed$$TwoStateAt.OT.value(TwoStateAt.OT$X: Ty, 
    this: Box
       where $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), $Heap));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap;



// OT.value: Type axiom
axiom 40 < $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty, $o: Box :: 
    { TwoStateAt.OT.value(TwoStateAt.OT$X, $o) } 
    $Is(TwoStateAt.OT.value(TwoStateAt.OT$X, $o), TInt));

// OT.value: Allocation axiom
axiom 40 < $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty, $h: Heap, $o: Box :: 
    { TwoStateAt.OT.value(TwoStateAt.OT$X, $o), $IsAlloc($o, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), $h) } 
    $IsGoodHeap($h) && $IsAlloc($o, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), $h)
       ==> $IsAlloc(TwoStateAt.OT.value(TwoStateAt.OT$X, $o), TInt, $h));

function {:inline} TwoStateAt.OT.sc(TwoStateAt.OT$X: Ty) : int
{
  LitInt(18)
}

procedure CheckWellformed$$TwoStateAt.OT.sc(TwoStateAt.OT$X: Ty);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap;



// OT.sc: Type axiom
axiom 43 < $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty :: 
    { TwoStateAt.OT.sc(TwoStateAt.OT$X) } 
    $Is(TwoStateAt.OT.sc(TwoStateAt.OT$X), TInt));

// OT.sc: Allocation axiom
axiom 43 < $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty, $h: Heap :: 
    { $IsAlloc(TwoStateAt.OT.sc(TwoStateAt.OT$X), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(TwoStateAt.OT.sc(TwoStateAt.OT$X), TInt, $h));

// function declaration for TwoStateAt.OT.F
function TwoStateAt.OT.F(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    this: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : int;

function TwoStateAt.OT.F#canCall(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    this: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : bool;

// frame axiom for TwoStateAt.OT.F
axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    this: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $h1, this, x#0, y#0, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
       && (TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $h0, this, x#0, y#0, c#0)
         || (
          $IsBox(x#0, TwoStateAt.OT$X)
           && $IsBox(y#0, TwoStateAt.OT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $h0, this, x#0, y#0, c#0)
       == TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $h1, this, x#0, y#0, c#0));

// consequence axiom for TwoStateAt.OT.F
axiom 15 <= $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty, 
      TwoStateAt.OT.F$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      this: Box, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0) } 
    TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
         || (15 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
           && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), $prevHeap)
           && $IsBox(x#0, TwoStateAt.OT$X)
           && $IsBox(y#0, TwoStateAt.OT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.OT.F#requires(Ty, Ty, Heap, Heap, Box, Box, Box, ref) : bool;

// #requires axiom for TwoStateAt.OT.F
axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $Heap: Heap, 
    this: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { TwoStateAt.OT.F#requires(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && 
      $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
       && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), $prevHeap)
       && $IsBox(x#0, TwoStateAt.OT$X)
       && $IsBox(y#0, TwoStateAt.OT.F$Y)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.OT.F#requires(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
       == (
        $IsAllocBox(x#0, TwoStateAt.OT$X, $prevHeap)
         && $IsAllocBox(y#0, TwoStateAt.OT.F$Y, $prevHeap)
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)));

// definition axiom for TwoStateAt.OT.F (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty, 
      TwoStateAt.OT.F$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      this: Box, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
    TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
         || (15 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
           && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), $prevHeap)
           && $IsBox(x#0, TwoStateAt.OT$X)
           && $IsBox(y#0, TwoStateAt.OT.F$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $Heap, this, x#0, y#0, c#0)
         == read($Heap, c#0, TwoStateAt.Cell.data)
           - read($prevHeap, c#0, TwoStateAt.Cell.data));

procedure CheckWellformed$$TwoStateAt.OT.F(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: Box
       where $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.F$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.F$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap));
  free requires 15 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.OT.F(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(529,22): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assert c#0 != null;
        b$reqreads#0 := $_Frame[c#0, TwoStateAt.Cell.data];
        assert c#0 != null;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, old($Heap), $Heap, this, x#0, y#0, c#0)
           == read($Heap, c#0, TwoStateAt.Cell.data)
             - read(old($Heap), c#0, TwoStateAt.Cell.data);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, old($Heap), $Heap, this, x#0, y#0, c#0), 
          TInt);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$TwoStateAt.OT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.L$Y: Ty, 
    this: Box
       where $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  free requires 16 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.OT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.OT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.L$Y: Ty, 
    this: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: L, CheckWellformed$$TwoStateAt.OT.L
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(534,19): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert c#0 != null;
    assume read(old($Heap), c#0, TwoStateAt.Cell.data)
       <= read($Heap, c#0, TwoStateAt.Cell.data);
    havoc n#0;
}



procedure Call$$TwoStateAt.OT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.L$Y: Ty, 
    this: Box
       where $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  requires $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.OT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.OT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.L$Y: Ty, 
    this: Box
       where $Is(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X))
         && $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.L$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.L$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0, $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.OT.L$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.OT.L(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.L$Y: Ty, 
    this: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: Box;
  var ##y#0: Box;
  var ##c#0: ref;

    // AddMethodImpl: L, Impl$$TwoStateAt.OT.L
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(536,4): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(537,9)
    assume true;
    ##x#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#0, TwoStateAt.OT$X, $Heap);
    ##y#0 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#0, TwoStateAt.OT.L$Y, $Heap);
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
    assert $IsAlloc(this, Tclass.TwoStateAt.OT(TwoStateAt.OT$X), old($Heap));
    assert $IsAllocBox(x#0, TwoStateAt.OT$X, old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt.OT.L$Y, old($Heap));
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assume TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0);
    assume TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0);
    assert $Is(TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0), 
      Tclass._System.nat());
    n#0 := TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.L$Y, old($Heap), $Heap, this, x#0, y#0, c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(537,21)"} true;
}



// function declaration for TwoStateAt.OT.G
function TwoStateAt.OT.G(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    ot#0: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : int;

function TwoStateAt.OT.G#canCall(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    ot#0: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   : bool;

// frame axiom for TwoStateAt.OT.G
axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    ot#0: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $h1, ot#0, x#0, y#0, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.OT.G#canCall(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $h0, ot#0, x#0, y#0, c#0)
         || (
          $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
           && $IsBox(x#0, TwoStateAt.OT$X)
           && $IsBox(y#0, TwoStateAt.OT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $h0, ot#0, x#0, y#0, c#0)
       == TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $h1, ot#0, x#0, y#0, c#0));

// consequence axiom for TwoStateAt.OT.G
axiom 17 <= $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty, 
      TwoStateAt.OT.G$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      ot#0: Box, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0) } 
    TwoStateAt.OT.G#canCall(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0)
         || (17 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
           && $IsBox(x#0, TwoStateAt.OT$X)
           && $IsBox(y#0, TwoStateAt.OT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.OT.G#requires(Ty, Ty, Heap, Heap, Box, Box, Box, ref) : bool;

// #requires axiom for TwoStateAt.OT.G
axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $Heap: Heap, 
    ot#0: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref :: 
  { TwoStateAt.OT.G#requires(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
       && $IsBox(x#0, TwoStateAt.OT$X)
       && $IsBox(y#0, TwoStateAt.OT.G$Y)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.OT.G#requires(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0)
       == (
        $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), $prevHeap)
         && $IsAllocBox(x#0, TwoStateAt.OT$X, $prevHeap)
         && $IsAllocBox(y#0, TwoStateAt.OT.G$Y, $prevHeap)
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)));

// definition axiom for TwoStateAt.OT.G (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall TwoStateAt.OT$X: Ty, 
      TwoStateAt.OT.G$Y: Ty, 
      $prevHeap: Heap, 
      $Heap: Heap, 
      ot#0: Box, 
      x#0: Box, 
      y#0: Box, 
      c#0: ref :: 
    { TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0), $IsGoodHeap($Heap) } 
    TwoStateAt.OT.G#canCall(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0)
         || (17 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
           && $IsBox(x#0, TwoStateAt.OT$X)
           && $IsBox(y#0, TwoStateAt.OT.G$Y)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0)
         && TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0)
           == TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap, $Heap, ot#0, x#0, y#0, c#0));

procedure CheckWellformed$$TwoStateAt.OT.G(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
         && $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.G$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.G$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap));
  free requires 17 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.OT.G(TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    ot#0: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: Box;
  var ##y#0: Box;
  var ##c#0: ref;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function G
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(539,29): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, TwoStateAt.OT$X, $Heap);
        ##y#0 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#0, TwoStateAt.OT.G$Y, $Heap);
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), old($Heap));
        assert $IsAllocBox(x#0, TwoStateAt.OT$X, old($Heap));
        assert $IsAllocBox(y#0, TwoStateAt.OT.G$Y, old($Heap));
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == ##c#0 ==> $_Frame[$o, $f]);
        assume TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, old($Heap), $Heap, ot#0, x#0, y#0, c#0);
        assume TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, old($Heap), $Heap, ot#0, x#0, y#0, c#0)
           == TwoStateAt.OT.F(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, old($Heap), $Heap, ot#0, x#0, y#0, c#0);
        assume TwoStateAt.OT.F#canCall(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, old($Heap), $Heap, ot#0, x#0, y#0, c#0);
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.OT.G(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, old($Heap), $Heap, ot#0, x#0, y#0, c#0), 
          TInt);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$TwoStateAt.OT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.M$Y: Ty, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
         && $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  free requires 18 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), previous$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.OT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.OT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.M$Y: Ty, 
    ot#0: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, CheckWellformed$$TwoStateAt.OT.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(544,26): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert c#0 != null;
    assume read(old($Heap), c#0, TwoStateAt.Cell.data)
       <= read($Heap, c#0, TwoStateAt.Cell.data);
    havoc n#0;
}



procedure Call$$TwoStateAt.OT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.M$Y: Ty, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
         && $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  requires $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), previous$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.OT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.OT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.M$Y: Ty, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TwoStateAt.OT$X))
         && $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), previous$Heap), 
    x#0: Box
       where $IsBox(x#0, TwoStateAt.OT$X) && $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt.OT.M$Y)
         && $IsAllocBox(y#0, TwoStateAt.OT.M$Y, previous$Heap), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap))
   returns (n#0: int where LitInt(0) <= n#0, $_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), previous$Heap);
  requires $IsAllocBox(x#0, TwoStateAt.OT$X, previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt.OT.M$Y, previous$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, TwoStateAt.Cell.data)
     <= read(current$Heap, c#0, TwoStateAt.Cell.data);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.OT.M(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.M$Y: Ty, 
    ot#0: Box, 
    x#0: Box, 
    y#0: Box, 
    c#0: ref)
   returns (n#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int where LitInt(0) <= $rhs##0;
  var x##0: Box;
  var y##0: Box;
  var c##0: ref;

    // AddMethodImpl: M, Impl$$TwoStateAt.OT.M
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(546,4): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(547,16)
    assume true;
    // TrCallStmt: Adding lhs with type nat
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := x#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := y#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assert $IsAllocBox(ot#0, #$OT(TwoStateAt.OT$X), old($Heap));
    assert $IsAllocBox(x#0, TwoStateAt.OT$X, old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt.OT.M$Y, old($Heap));
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$TwoStateAt.OT.L(old($Heap), $Heap, TwoStateAt.OT$X, TwoStateAt.OT.M$Y, ot#0, x##0, y##0, c##0);
    // TrCallStmt: After ProcessCallStmt
    n#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(547,24)"} true;
}



const unique class.TwoStateAt.__default: ClassName;

function Tclass.TwoStateAt.__default() : Ty;

const unique Tagclass.TwoStateAt.__default: TyTag;

// Tclass.TwoStateAt.__default Tag
axiom Tag(Tclass.TwoStateAt.__default()) == Tagclass.TwoStateAt.__default
   && TagFamily(Tclass.TwoStateAt.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TwoStateAt.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TwoStateAt.__default()) } 
  $IsBox(bx, Tclass.TwoStateAt.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TwoStateAt.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TwoStateAt.__default()) } 
  $Is($o, Tclass.TwoStateAt.__default())
     <==> $o == null || dtype($o) == Tclass.TwoStateAt.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TwoStateAt.__default(), $h) } 
  $IsAlloc($o, Tclass.TwoStateAt.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for TwoStateAt._default.SP
function TwoStateAt.__default.SP(TwoStateAt._default.SP$Y: Ty, $prevHeap: Heap, $heap: Heap, c#0: ref, y#0: Box)
   : int;

function TwoStateAt.__default.SP#canCall(TwoStateAt._default.SP$Y: Ty, $prevHeap: Heap, $heap: Heap, c#0: ref, y#0: Box)
   : bool;

// frame axiom for TwoStateAt.__default.SP
axiom (forall TwoStateAt._default.SP$Y: Ty, 
    $prevHeap: Heap, 
    $h0: Heap, 
    $h1: Heap, 
    c#0: ref, 
    y#0: Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, $prevHeap, $h1, c#0, y#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.__default.SP#canCall(TwoStateAt._default.SP$Y, $prevHeap, $h0, c#0, y#0)
         || ($Is(c#0, Tclass.TwoStateAt.Cell()) && $IsBox(y#0, TwoStateAt._default.SP$Y)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, $prevHeap, $h0, c#0, y#0)
       == TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, $prevHeap, $h1, c#0, y#0));

// consequence axiom for TwoStateAt.__default.SP
axiom 1 <= $FunctionContextHeight
   ==> (forall TwoStateAt._default.SP$Y: Ty, $prevHeap: Heap, $Heap: Heap, c#0: ref, y#0: Box :: 
    { TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, $prevHeap, $Heap, c#0, y#0) } 
    TwoStateAt.__default.SP#canCall(TwoStateAt._default.SP$Y, $prevHeap, $Heap, c#0, y#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell())
           && $IsBox(y#0, TwoStateAt._default.SP$Y))
       ==> true);

function TwoStateAt.__default.SP#requires(Ty, Heap, Heap, ref, Box) : bool;

// #requires axiom for TwoStateAt.__default.SP
axiom (forall TwoStateAt._default.SP$Y: Ty, $prevHeap: Heap, $Heap: Heap, c#0: ref, y#0: Box :: 
  { TwoStateAt.__default.SP#requires(TwoStateAt._default.SP$Y, $prevHeap, $Heap, c#0, y#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsBox(y#0, TwoStateAt._default.SP$Y)
     ==> TwoStateAt.__default.SP#requires(TwoStateAt._default.SP$Y, $prevHeap, $Heap, c#0, y#0)
       == ($IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)
         && $IsAllocBox(y#0, TwoStateAt._default.SP$Y, $prevHeap)));

// definition axiom for TwoStateAt.__default.SP (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall TwoStateAt._default.SP$Y: Ty, $prevHeap: Heap, $Heap: Heap, c#0: ref, y#0: Box :: 
    { TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, $prevHeap, $Heap, c#0, y#0), $IsGoodHeap($Heap) } 
    TwoStateAt.__default.SP#canCall(TwoStateAt._default.SP$Y, $prevHeap, $Heap, c#0, y#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell())
           && $IsBox(y#0, TwoStateAt._default.SP$Y))
       ==> TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, $prevHeap, $Heap, c#0, y#0)
         == read($prevHeap, c#0, TwoStateAt.Cell.data)
           + read($Heap, c#0, TwoStateAt.Cell.data));

procedure CheckWellformed$$TwoStateAt.__default.SP(TwoStateAt._default.SP$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.SP$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.SP$Y, previous$Heap));
  free requires 1 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.__default.SP(TwoStateAt._default.SP$Y: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref, 
    y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SP
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(281,20): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assert c#0 != null;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert c#0 != null;
        b$reqreads#0 := $_Frame[c#0, TwoStateAt.Cell.data];
        assume TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, old($Heap), $Heap, c#0, y#0)
           == read(old($Heap), c#0, TwoStateAt.Cell.data)
             + read($Heap, c#0, TwoStateAt.Cell.data);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.__default.SP(TwoStateAt._default.SP$Y, old($Heap), $Heap, c#0, y#0), 
          TInt);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$TwoStateAt.__default.Test(TwoStateAt._default.Test$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap), 
    b#0: bool, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.Test$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.__default.Test(TwoStateAt._default.Test$Y: Ty, c#0: ref, b#0: bool, y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Test, CheckWellformed$$TwoStateAt.__default.Test
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(287,9): initial state"} true;
    assert c#0 != null;
    assume read($Heap, c#0, TwoStateAt.Cell.data) == LitInt(2);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$TwoStateAt.__default.Test(TwoStateAt._default.Test$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap), 
    b#0: bool, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.Test$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap));
  // user-defined preconditions
  requires read($Heap, c#0, TwoStateAt.Cell.data) == LitInt(2);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.Test(TwoStateAt._default.Test$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap), 
    b#0: bool, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.Test$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, c#0, TwoStateAt.Cell.data) == LitInt(2);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.Test(TwoStateAt._default.Test$Y: Ty, c#0: ref, b#0: bool, y#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##y#0: Box;
  var $rhs#0: int;
  var $Heap_at_0: Heap;
  var ##c#0: ref;
  var ##y#1: Box;
  var ##c#1: ref;
  var ##y#2: Box;
  var $rhs#1: int;
  var ##c#2: ref;
  var ##y#3: Box;
  var newtype$check#0: int;
  var ##c#3: ref;
  var ##y#4: bv3;
  var $rhs#0_0: int;
  var $rhs#2: int;
  var $Heap_at_1: Heap;
  var ##y#5: Box;
  var ##y#6: int;
  var w#Z#0: int;
  var let#0#0#0: int;
  var ##c#4: ref;
  var ##y#7: Box;
  var ##c#5: ref;
  var ##y#8: Box;
  var u#0: int;
  var ##c#6: ref;
  var ##y#9: int;
  var ##c#7: ref;
  var ##y#10: Box;

    // AddMethodImpl: Test, Impl$$TwoStateAt.__default.Test
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(290,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(291,5)
    assert {:subsumption 0} c#0 != null;
    ##y#0 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#0, TwoStateAt._default.Test$Y, $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, old($Heap));
    assume TwoStateAt.Cell.Plus#canCall(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0);
    assume TwoStateAt.Cell.Plus#canCall(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0);
    assert TwoStateAt.Cell.Plus(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0)
       == LitInt(4);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(292,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, TwoStateAt.Cell.data) + 3;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(292,24)"} true;
    $Heap_at_0 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(294,5)
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
    ##y#1 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#1, TwoStateAt._default.Test$Y, $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, old($Heap));
    assume TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0);
    assume TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0);
    assert TwoStateAt.Cell.Sum(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0)
       == LitInt(7);

  after_0:
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(295,5)
    ##c#1 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#1, Tclass.TwoStateAt.Cell(), $Heap);
    ##y#2 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#2, TwoStateAt._default.Test$Y, $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
    assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap_at_0);
    assume TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0);
    assume TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0);
    assert TwoStateAt.Cell.Sum(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0)
       == LitInt(10);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(297,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#1 := read($Heap, c#0, TwoStateAt.Cell.data) + 1;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(297,24)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(298,5)
    ##c#2 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#2, Tclass.TwoStateAt.Cell(), $Heap);
    ##y#3 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#3, TwoStateAt._default.Test$Y, $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, old($Heap));
    assume TwoStateAt.__default.SP#canCall(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0);
    assume TwoStateAt.__default.SP#canCall(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0);
    assert TwoStateAt.__default.SP(TwoStateAt._default.Test$Y, old($Heap), $Heap, c#0, y#0)
       == LitInt(8);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(299,5)
    newtype$check#0 := LitInt(0);
    assert 0 <= newtype$check#0 && newtype$check#0 < 8;
    ##c#3 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#3, Tclass.TwoStateAt.Cell(), $Heap);
    ##y#4 := 0bv3;
    // assume allocatedness for argument to function
    assume $IsAlloc(##y#4, TBitvector(3), $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
    assume TwoStateAt.__default.SP#canCall(TBitvector(3), $Heap_at_0, $Heap, c#0, $Box(0bv3));
    assume TwoStateAt.__default.SP#canCall(TBitvector(3), $Heap_at_0, $Heap, c#0, $Box(0bv3));
    assert TwoStateAt.__default.SP(TBitvector(3), $Heap_at_0, $Heap, c#0, $Box(0bv3))
       == LitInt(11);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(301,5)
    assume true;
    if (b#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(302,14)
        assert c#0 != null;
        assume true;
        assert $_Frame[c#0, TwoStateAt.Cell.data];
        assert c#0 != null;
        assume true;
        $rhs#0_0 := read($Heap, c#0, TwoStateAt.Cell.data) + 10;
        $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(302,27)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(304,14)
        assert c#0 != null;
        assume true;
        assert $_Frame[c#0, TwoStateAt.Cell.data];
        assert c#0 != null;
        assume true;
        $rhs#2 := read($Heap, c#0, TwoStateAt.Cell.data) + 20;
        $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(304,27)"} true;
    }

    $Heap_at_1 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(308,5)
    assert {:subsumption 0} c#0 != null;
    ##y#5 := y#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##y#5, TwoStateAt._default.Test$Y, $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
    assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap_at_0);
    assume TwoStateAt.Cell.Plus#canCall(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0);
    if (TwoStateAt.Cell.Plus(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0)
       != LitInt(21))
    {
        assert {:subsumption 0} c#0 != null;
        ##y#6 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#6, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
    }

    assume TwoStateAt.Cell.Plus#canCall(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0)
       && (TwoStateAt.Cell.Plus(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0)
           != LitInt(21)
         ==> TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0))));
    assert TwoStateAt.Cell.Plus(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0)
         == LitInt(21)
       || TwoStateAt.Cell.Plus(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)))
         == LitInt(31);

  after_1:
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(309,5)
    if (b#0)
    {
        havoc w#Z#0;
        assume true;
        ##c#4 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#4, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#7 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#7, TwoStateAt._default.Test$Y, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_1);
        assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap_at_1);
        assume TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0);
        assume let#0#0#0
           == TwoStateAt.Cell.Sum(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0);
        assume TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, TInt);
        assume w#Z#0 == let#0#0#0;
    }

    assume b#0
       ==> TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0);
    assert {:subsumption 0} b#0
       ==> (var w#0 := TwoStateAt.Cell.Sum(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0); 
          w#0)
         == LitInt(32);
    assume b#0
       ==> (var w#0 := TwoStateAt.Cell.Sum(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0); 
          w#0)
         == LitInt(32);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(310,5)
    if (!b#0)
    {
        ##c#5 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#5, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#8 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#8, TwoStateAt._default.Test$Y, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_1);
        assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap_at_1);
        assume TwoStateAt.__default.SP#canCall(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0);
    }

    assume !b#0
       ==> TwoStateAt.__default.SP#canCall(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0);
    assert {:subsumption 0} !b#0
       ==> TwoStateAt.__default.SP(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0)
         == LitInt(52);
    assume !b#0
       ==> TwoStateAt.__default.SP(TwoStateAt._default.Test$Y, $Heap_at_1, $Heap, c#0, y#0)
         == LitInt(52);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(311,17)
    assume true;
    ##c#6 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#6, Tclass.TwoStateAt.Cell(), $Heap);
    ##y#9 := LitInt(0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##y#9, TInt, $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
    assume TwoStateAt.__default.SP#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
    assume TwoStateAt.__default.SP#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
    u#0 := TwoStateAt.__default.SP(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(311,32)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(312,5)
    if (b#0)
    {
    }

    assume true;
    assert {:subsumption 0} b#0 ==> u#0 == LitInt(21);
    assume b#0 ==> u#0 == LitInt(21);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(313,5)
    if (!b#0)
    {
        ##c#7 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#7, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#10 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#10, TwoStateAt._default.Test$Y, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assert $IsAllocBox(y#0, TwoStateAt._default.Test$Y, $Heap_at_0);
        assume TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0);
    }

    assume !b#0
       ==> TwoStateAt.Cell.Sum#canCall(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0);
    assert {:subsumption 0} !b#0
       ==> TwoStateAt.Cell.Sum(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0)
         == LitInt(30);
    assume !b#0
       ==> TwoStateAt.Cell.Sum(TwoStateAt._default.Test$Y, $Heap_at_0, $Heap, c#0, y#0)
         == LitInt(30);
}



procedure CheckWellformed$$TwoStateAt.__default.TwoLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt._default.TwoLemma$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.TwoLemma$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, previous$Heap));
  free requires 20 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.__default.TwoLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt._default.TwoLemma$Y: Ty, 
    c#0: ref, 
    y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: ref;
  var ##y#0: int;
  var ##c#1: ref;
  var ##y#1: Box;
  var ##c#2: ref;
  var ##y#2: Box;
  var ##y#3: Box;

    // AddMethodImpl: TwoLemma, CheckWellformed$$TwoStateAt.__default.TwoLemma
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(316,17): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
    ##y#0 := LitInt(0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##y#0, TInt, $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assume TwoStateAt.Cell.Sum#canCall(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
    assume Mul(LitInt(2), read(old($Heap), c#0, TwoStateAt.Cell.data))
       <= TwoStateAt.Cell.Sum(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(318,24): post-state"} true;
    if (*)
    {
        assert c#0 != null;
        assume LitInt(0) <= read($Heap, c#0, TwoStateAt.Cell.data);
        assert c#0 != null;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        ##c#1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#1 := y#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##y#1, TwoStateAt._default.TwoLemma$Y, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, old($Heap));
        assume TwoStateAt.__default.SP#canCall(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0);
        if (read(old($Heap), c#0, TwoStateAt.Cell.data)
           <= TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0))
        {
            ##c#2 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#2, Tclass.TwoStateAt.Cell(), $Heap);
            ##y#2 := y#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##y#2, TwoStateAt._default.TwoLemma$Y, $Heap);
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
            assert $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, old($Heap));
            assume TwoStateAt.__default.SP#canCall(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0);
            assert c#0 != null;
            ##y#3 := y#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##y#3, TwoStateAt._default.TwoLemma$Y, $Heap);
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
            assert $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, old($Heap));
            assume TwoStateAt.Cell.Plus#canCall(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0);
        }

        assume read(old($Heap), c#0, TwoStateAt.Cell.data)
             <= TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0)
           && TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0)
             == TwoStateAt.Cell.Plus(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0);
    }
    else
    {
        assume LitInt(0) <= read($Heap, c#0, TwoStateAt.Cell.data)
           ==> read(old($Heap), c#0, TwoStateAt.Cell.data)
               <= TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0)
             && TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0)
               == TwoStateAt.Cell.Plus(TwoStateAt._default.TwoLemma$Y, old($Heap), $Heap, c#0, y#0);
    }
}



procedure Call$$TwoStateAt.__default.TwoLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt._default.TwoLemma$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.TwoLemma$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, previous$Heap));
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, previous$Heap);
  // user-defined preconditions
  requires Mul(LitInt(2), read(previous$Heap, c#0, TwoStateAt.Cell.data))
     <= TwoStateAt.Cell.Sum(TInt, previous$Heap, current$Heap, c#0, $Box(LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures LitInt(0) <= read(current$Heap, c#0, TwoStateAt.Cell.data)
     ==> TwoStateAt.__default.SP#canCall(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
       && (read(previous$Heap, c#0, TwoStateAt.Cell.data)
           <= TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
         ==> TwoStateAt.__default.SP#canCall(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
           && TwoStateAt.Cell.Plus#canCall(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0));
  ensures LitInt(0) <= read(current$Heap, c#0, TwoStateAt.Cell.data)
     ==> read(previous$Heap, c#0, TwoStateAt.Cell.data)
       <= TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0);
  ensures LitInt(0) <= read(current$Heap, c#0, TwoStateAt.Cell.data)
     ==> TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
       == TwoStateAt.Cell.Plus(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.__default.TwoLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt._default.TwoLemma$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.TwoLemma$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  requires $IsAllocBox(y#0, TwoStateAt._default.TwoLemma$Y, previous$Heap);
  // user-defined preconditions
  requires Mul(LitInt(2), read(previous$Heap, c#0, TwoStateAt.Cell.data))
     <= TwoStateAt.Cell.Sum(TInt, previous$Heap, current$Heap, c#0, $Box(LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures LitInt(0) <= read(current$Heap, c#0, TwoStateAt.Cell.data)
     ==> TwoStateAt.__default.SP#canCall(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
       && (read(previous$Heap, c#0, TwoStateAt.Cell.data)
           <= TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
         ==> TwoStateAt.__default.SP#canCall(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
           && TwoStateAt.Cell.Plus#canCall(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0));
  ensures LitInt(0) <= read(current$Heap, c#0, TwoStateAt.Cell.data)
     ==> read(previous$Heap, c#0, TwoStateAt.Cell.data)
       <= TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0);
  ensures LitInt(0) <= read(current$Heap, c#0, TwoStateAt.Cell.data)
     ==> TwoStateAt.__default.SP(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0)
       == TwoStateAt.Cell.Plus(TwoStateAt._default.TwoLemma$Y, previous$Heap, current$Heap, c#0, y#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.__default.TwoLemma(previous$Heap: Heap, 
    current$Heap: Heap, 
    TwoStateAt._default.TwoLemma$Y: Ty, 
    c#0: ref, 
    y#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TwoLemma, Impl$$TwoStateAt.__default.TwoLemma
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(319,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$TwoStateAt.__default.CallLemmas(TwoStateAt._default.CallLemmas$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap), 
    b#0: bool, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.CallLemmas$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.CallLemmas$Y, $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.CallLemmas(TwoStateAt._default.CallLemmas$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap), 
    b#0: bool, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.CallLemmas$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.CallLemmas$Y, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.CallLemmas(TwoStateAt._default.CallLemmas$Y: Ty, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap), 
    b#0: bool, 
    y#0: Box
       where $IsBox(y#0, TwoStateAt._default.CallLemmas$Y)
         && $IsAllocBox(y#0, TwoStateAt._default.CallLemmas$Y, $Heap))
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.CallLemmas(TwoStateAt._default.CallLemmas$Y: Ty, c#0: ref, b#0: bool, y#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $Heap_at_0: Heap;
  var c##0_0: ref;
  var y##0_0: Box;
  var $rhs#1: int;
  var $Heap_at_1: Heap;
  var c##0: ref;
  var y##0: Box;
  var $rhs#1_0: int;
  var c##1_0: ref;
  var y##1_0: Box;
  var $rhs#2: int;
  var y##1: Box;
  var y##2: int;

    // AddMethodImpl: CallLemmas, Impl$$TwoStateAt.__default.CallLemmas
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(324,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(325,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, TwoStateAt.Cell.data) + 1;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(325,24)"} true;
    $Heap_at_0 := $Heap;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(327,5)
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assume true;
    if (LitInt(-1) <= read(old($Heap), c#0, TwoStateAt.Cell.data))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(328,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##0_0 := y#0;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert $IsAllocBox(y#0, TwoStateAt._default.CallLemmas$Y, old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.__default.TwoLemma(old($Heap), $Heap, TwoStateAt._default.CallLemmas$Y, c##0_0, y##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(328,20)"} true;
    }
    else
    {
    }

  after_0:
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(331,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#1 := read($Heap, c#0, TwoStateAt.Cell.data) + 4;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(331,24)"} true;
    $Heap_at_1 := $Heap;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(333,21)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := y#0;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
    assert $IsAllocBox(y#0, TwoStateAt._default.CallLemmas$Y, $Heap_at_0);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$TwoStateAt.__default.TwoLemma($Heap_at_0, $Heap, TwoStateAt._default.CallLemmas$Y, c##0, y##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(333,26)"} true;

  after_1:
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(335,5)
    assume true;
    if (b#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(336,14)
        assert c#0 != null;
        assume true;
        assert $_Frame[c#0, TwoStateAt.Cell.data];
        assert c#0 != null;
        assume true;
        $rhs#1_0 := read($Heap, c#0, TwoStateAt.Cell.data) - 10;
        $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#1_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(336,27)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(337,24)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##1_0 := y#0;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_1);
        assert $IsAllocBox(y#0, TwoStateAt._default.CallLemmas$Y, $Heap_at_1);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.__default.TwoLemma($Heap_at_1, $Heap, TwoStateAt._default.CallLemmas$Y, c##1_0, y##1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(337,29)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(339,14)
        assert c#0 != null;
        assume true;
        assert $_Frame[c#0, TwoStateAt.Cell.data];
        assert c#0 != null;
        assume true;
        $rhs#2 := read($Heap, c#0, TwoStateAt.Cell.data) + 2;
        $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(339,26)"} true;
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(341,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert c#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##1 := y#0;
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert $IsAllocBox(y#0, TwoStateAt._default.CallLemmas$Y, old($Heap));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$TwoStateAt.Cell.LL(old($Heap), $Heap, TwoStateAt._default.CallLemmas$Y, c#0, y##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(341,11)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(342,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert c#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##2 := LitInt(0);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$TwoStateAt.Cell.LL(old($Heap), $Heap, TInt, c#0, $Box(y##2));
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(342,11)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(343,5)
    assume true;
    assert !b#0;
}



// function declaration for TwoStateAt._default.Opaque
function TwoStateAt.__default.Opaque($ly: LayerType, $prevHeap: Heap, $heap: Heap, c#0: ref) : int;

function TwoStateAt.__default.Opaque#canCall($prevHeap: Heap, $heap: Heap, c#0: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $prevHeap: Heap, $Heap: Heap, c#0: ref :: 
  { TwoStateAt.__default.Opaque($LS($ly), $prevHeap, $Heap, c#0) } 
  TwoStateAt.__default.Opaque($LS($ly), $prevHeap, $Heap, c#0)
     == TwoStateAt.__default.Opaque($ly, $prevHeap, $Heap, c#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $prevHeap: Heap, $Heap: Heap, c#0: ref :: 
  { TwoStateAt.__default.Opaque(AsFuelBottom($ly), $prevHeap, $Heap, c#0) } 
  TwoStateAt.__default.Opaque($ly, $prevHeap, $Heap, c#0)
     == TwoStateAt.__default.Opaque($LZ, $prevHeap, $Heap, c#0));

// frame axiom for TwoStateAt.__default.Opaque
axiom (forall $ly: LayerType, $prevHeap: Heap, $h0: Heap, $h1: Heap, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.__default.Opaque($ly, $prevHeap, $h1, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.__default.Opaque#canCall($prevHeap, $h0, c#0)
         || $Is(c#0, Tclass.TwoStateAt.Cell()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      false ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.__default.Opaque($ly, $prevHeap, $h0, c#0)
       == TwoStateAt.__default.Opaque($ly, $prevHeap, $h1, c#0));

// consequence axiom for TwoStateAt.__default.Opaque
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $prevHeap: Heap, $Heap: Heap, c#0: ref :: 
    { TwoStateAt.__default.Opaque($ly, $prevHeap, $Heap, c#0) } 
    TwoStateAt.__default.Opaque#canCall($prevHeap, $Heap, c#0)
         || (23 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.__default.Opaque#requires(LayerType, Heap, Heap, ref) : bool;

// #requires axiom for TwoStateAt.__default.Opaque
axiom (forall $ly: LayerType, $prevHeap: Heap, $Heap: Heap, c#0: ref :: 
  { TwoStateAt.__default.Opaque#requires($ly, $prevHeap, $Heap, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.__default.Opaque#requires($ly, $prevHeap, $Heap, c#0)
       == $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap));

// definition axiom for TwoStateAt.__default.Opaque (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $prevHeap: Heap, $Heap: Heap, c#0: ref :: 
    { TwoStateAt.__default.Opaque($LS($ly), $prevHeap, $Heap, c#0), $IsGoodHeap($Heap) } 
    TwoStateAt.__default.Opaque#canCall($prevHeap, $Heap, c#0)
         || (23 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.__default.Opaque($LS($ly), $prevHeap, $Heap, c#0)
         == read($prevHeap, c#0, TwoStateAt.Cell.data) + 12);

// definition axiom for TwoStateAt.__default.Opaque for all literals (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $prevHeap: Heap, $Heap: Heap, c#0: ref :: 
    {:weight 3} { TwoStateAt.__default.Opaque($LS($ly), $prevHeap, $Heap, Lit(c#0)), $IsGoodHeap($Heap) } 
    TwoStateAt.__default.Opaque#canCall($prevHeap, $Heap, Lit(c#0))
         || (23 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.__default.Opaque($LS($ly), $prevHeap, $Heap, Lit(c#0))
         == read($prevHeap, Lit(c#0), TwoStateAt.Cell.data) + 12);

procedure {:opaque} CheckWellformed$$TwoStateAt.__default.Opaque(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap));
  free requires 23 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation {:opaque} CheckWellformed$$TwoStateAt.__default.Opaque(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function Opaque
    $Heap := current$Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(346,30): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert c#0 != null;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.__default.Opaque(StartFuel_TwoStateAt._default.Opaque, old($Heap), $Heap, c#0)
           == read(old($Heap), c#0, TwoStateAt.Cell.data) + 12;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(TwoStateAt.__default.Opaque(StartFuel_TwoStateAt._default.Opaque, old($Heap), $Heap, c#0), 
          TInt);
    }
}



procedure CheckWellformed$$TwoStateAt.__default.UseOpaque(c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TwoStateAt.__default.UseOpaque(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: UseOpaque, CheckWellformed$$TwoStateAt.__default.UseOpaque
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(347,9): initial state"} true;
    assert c#0 != null;
    assume read($Heap, c#0, TwoStateAt.Cell.data) == LitInt(100);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$TwoStateAt.__default.UseOpaque(c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap));
  // user-defined preconditions
  requires read($Heap, c#0, TwoStateAt.Cell.data) == LitInt(100);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.UseOpaque(c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, c#0, TwoStateAt.Cell.data) == LitInt(100);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.UseOpaque(c#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $Heap_at_0: Heap;
  var $rhs#1: int;
  var y112#0: int;
  var ##c#0: ref;
  var y117#0: int;
  var ##c#1: ref;

    // AddMethodImpl: UseOpaque, Impl$$TwoStateAt.__default.UseOpaque
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(350,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(351,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, TwoStateAt.Cell.data) + 5;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(351,24)"} true;
    $Heap_at_0 := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(353,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#1 := read($Heap, c#0, TwoStateAt.Cell.data) + 2;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(353,24)"} true;

  after_0:
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(355,14)
    assume true;
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, Tclass.TwoStateAt.Cell(), $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
    assume TwoStateAt.__default.Opaque#canCall(old($Heap), $Heap, c#0);
    assume TwoStateAt.__default.Opaque#canCall(old($Heap), $Heap, c#0);
    y112#0 := TwoStateAt.__default.Opaque(StartFuel_TwoStateAt._default.Opaque, old($Heap), $Heap, c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(355,25)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(356,14)
    assume true;
    ##c#1 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#1, Tclass.TwoStateAt.Cell(), $Heap);
    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
    assume TwoStateAt.__default.Opaque#canCall($Heap_at_0, $Heap, c#0);
    assume TwoStateAt.__default.Opaque#canCall($Heap_at_0, $Heap, c#0);
    y117#0 := TwoStateAt.__default.Opaque(StartFuel_TwoStateAt._default.Opaque, $Heap_at_0, $Heap, c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(356,27)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(358,5)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(359,7)
        assume true;
        assert y112#0 == LitInt(112);
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(360,12)
        if (*)
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(361,7)
            assume true;
            assert y117#0 == LitInt(117);
        }
        else
        {
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(363,7)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(363,20)
            // TrCallStmt: Before ProcessCallStmt
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$TwoStateAt.__default.reveal__Opaque(old($Heap), $Heap);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(363,21)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(364,7)
            assume true;
            assert y112#0 == LitInt(112);
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(365,7)
            assume true;
            assert y117#0 == LitInt(117);
        }
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(367,5)
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert read($Heap, c#0, TwoStateAt.Cell.data) == LitInt(107);
}



// function declaration for TwoStateAt._default.FuncUseOpaque
function TwoStateAt.__default.FuncUseOpaque($prevHeap: Heap, $heap: Heap, c#0: ref, b#0: bool) : int;

function TwoStateAt.__default.FuncUseOpaque#canCall($prevHeap: Heap, $heap: Heap, c#0: ref, b#0: bool) : bool;

// frame axiom for TwoStateAt.__default.FuncUseOpaque
axiom (forall $prevHeap: Heap, $h0: Heap, $h1: Heap, c#0: ref, b#0: bool :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.__default.FuncUseOpaque($prevHeap, $h1, c#0, b#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.__default.FuncUseOpaque#canCall($prevHeap, $h0, c#0, b#0)
         || $Is(c#0, Tclass.TwoStateAt.Cell()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      false ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.__default.FuncUseOpaque($prevHeap, $h0, c#0, b#0)
       == TwoStateAt.__default.FuncUseOpaque($prevHeap, $h1, c#0, b#0));

// consequence axiom for TwoStateAt.__default.FuncUseOpaque
axiom 26 <= $FunctionContextHeight
   ==> (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, b#0: bool :: 
    { TwoStateAt.__default.FuncUseOpaque($prevHeap, $Heap, c#0, b#0) } 
    TwoStateAt.__default.FuncUseOpaque#canCall($prevHeap, $Heap, c#0, b#0)
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.__default.FuncUseOpaque#requires(Heap, Heap, ref, bool) : bool;

// #requires axiom for TwoStateAt.__default.FuncUseOpaque
axiom (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, b#0: bool :: 
  { TwoStateAt.__default.FuncUseOpaque#requires($prevHeap, $Heap, c#0, b#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.__default.FuncUseOpaque#requires($prevHeap, $Heap, c#0, b#0)
       == ($IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap)
         && $IsAlloc(b#0, TBool, $prevHeap)));

const MoreFuel_TwoStateAt._default.Opaque0: LayerType;

const MoreFuel_TwoStateAt._default.Opaque1: LayerType;

// definition axiom for TwoStateAt.__default.FuncUseOpaque (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, b#0: bool :: 
    { TwoStateAt.__default.FuncUseOpaque($prevHeap, $Heap, c#0, b#0), $IsGoodHeap($Heap) } 
    TwoStateAt.__default.FuncUseOpaque#canCall($prevHeap, $Heap, c#0, b#0)
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> StartFuel_TwoStateAt._default.Opaque
           == $LS(MoreFuel_TwoStateAt._default.Opaque0)
         && StartFuelAssert_TwoStateAt._default.Opaque
           == $LS($LS(MoreFuel_TwoStateAt._default.Opaque0))
         && AsFuelBottom(MoreFuel_TwoStateAt._default.Opaque0)
           == MoreFuel_TwoStateAt._default.Opaque0
         && StartFuel_TwoStateAt._default.Opaque
           == $LS(MoreFuel_TwoStateAt._default.Opaque1)
         && StartFuelAssert_TwoStateAt._default.Opaque
           == $LS($LS(MoreFuel_TwoStateAt._default.Opaque1))
         && AsFuelBottom(MoreFuel_TwoStateAt._default.Opaque1)
           == MoreFuel_TwoStateAt._default.Opaque1
         && TwoStateAt.__default.FuncUseOpaque($prevHeap, $Heap, c#0, b#0) == LitInt(10));

const MoreFuel_TwoStateAt._default.Opaque2: LayerType;

const MoreFuel_TwoStateAt._default.Opaque3: LayerType;

// definition axiom for TwoStateAt.__default.FuncUseOpaque for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, b#0: bool :: 
    {:weight 3} { TwoStateAt.__default.FuncUseOpaque($prevHeap, $Heap, Lit(c#0), Lit(b#0)), $IsGoodHeap($Heap) } 
    TwoStateAt.__default.FuncUseOpaque#canCall($prevHeap, $Heap, Lit(c#0), Lit(b#0))
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell()))
       ==> StartFuel_TwoStateAt._default.Opaque
           == $LS(MoreFuel_TwoStateAt._default.Opaque2)
         && StartFuelAssert_TwoStateAt._default.Opaque
           == $LS($LS(MoreFuel_TwoStateAt._default.Opaque2))
         && AsFuelBottom(MoreFuel_TwoStateAt._default.Opaque2)
           == MoreFuel_TwoStateAt._default.Opaque2
         && StartFuel_TwoStateAt._default.Opaque
           == $LS(MoreFuel_TwoStateAt._default.Opaque3)
         && StartFuelAssert_TwoStateAt._default.Opaque
           == $LS($LS(MoreFuel_TwoStateAt._default.Opaque3))
         && AsFuelBottom(MoreFuel_TwoStateAt._default.Opaque3)
           == MoreFuel_TwoStateAt._default.Opaque3
         && TwoStateAt.__default.FuncUseOpaque($prevHeap, $Heap, Lit(c#0), Lit(b#0))
           == LitInt(10));

procedure CheckWellformed$$TwoStateAt.__default.FuncUseOpaque(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    b#0: bool);
  free requires 26 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



procedure CheckWellformed$$TwoStateAt.__default.Allocatedness__Function();
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.Allocatedness__Function();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.Allocatedness__Function() returns ($_reverifyPost: bool);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function TwoStateAt.Cell.Plus#Handle(Ty, Heap, ref) : HandleType;

axiom (forall TwoStateAt.Cell.Plus$Y: Ty, 
    $prevHeap: Heap, 
    $self: ref, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Apply1(TwoStateAt.Cell.Plus$Y, 
      TInt, 
      $heap, 
      TwoStateAt.Cell.Plus#Handle(TwoStateAt.Cell.Plus$Y, $prevHeap, $self), 
      $fh$0x#0) } 
  Apply1(TwoStateAt.Cell.Plus$Y, 
      TInt, 
      $heap, 
      TwoStateAt.Cell.Plus#Handle(TwoStateAt.Cell.Plus$Y, $prevHeap, $self), 
      $fh$0x#0)
     == $Box(TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $heap, $self, $fh$0x#0)));

axiom (forall TwoStateAt.Cell.Plus$Y: Ty, 
    $prevHeap: Heap, 
    $self: ref, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Requires1(TwoStateAt.Cell.Plus$Y, 
      TInt, 
      $heap, 
      TwoStateAt.Cell.Plus#Handle(TwoStateAt.Cell.Plus$Y, $prevHeap, $self), 
      $fh$0x#0) } 
  Requires1(TwoStateAt.Cell.Plus$Y, 
      TInt, 
      $heap, 
      TwoStateAt.Cell.Plus#Handle(TwoStateAt.Cell.Plus$Y, $prevHeap, $self), 
      $fh$0x#0)
     == TwoStateAt.Cell.Plus#requires(TwoStateAt.Cell.Plus$Y, $prevHeap, $heap, $self, $fh$0x#0));

axiom (forall $bx: Box, 
    TwoStateAt.Cell.Plus$Y: Ty, 
    $prevHeap: Heap, 
    $self: ref, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Reads1(TwoStateAt.Cell.Plus$Y, 
      TInt, 
      $heap, 
      TwoStateAt.Cell.Plus#Handle(TwoStateAt.Cell.Plus$Y, $prevHeap, $self), 
      $fh$0x#0)[$bx] } 
  Reads1(TwoStateAt.Cell.Plus$Y, 
      TInt, 
      $heap, 
      TwoStateAt.Cell.Plus#Handle(TwoStateAt.Cell.Plus$Y, $prevHeap, $self), 
      $fh$0x#0)[$bx]
     == 
    ($Unbox($bx): ref
     == $self));

axiom (forall TwoStateAt.Cell.Plus$Y: Ty, 
    $prevHeap: Heap, 
    $self: ref, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $heap, $self, $fh$0x#0) } 
  TwoStateAt.Cell.Plus(TwoStateAt.Cell.Plus$Y, $prevHeap, $heap, $self, $fh$0x#0)
     == $Unbox(Apply1(TwoStateAt.Cell.Plus$Y, 
        TInt, 
        $heap, 
        TwoStateAt.Cell.Plus#Handle(TwoStateAt.Cell.Plus$Y, $prevHeap, $self), 
        $fh$0x#0)): int);

implementation Impl$$TwoStateAt.__default.Allocatedness__Function() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $Heap_at_0: Heap;
  var c#0: ref
     where $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var $Heap_at_1: Heap;
  var $Heap_at_2: Heap;
  var $rhs#0: int;
  var $Heap_at_3: Heap;
  var a#0_0: HandleType
     where $Is(a#0_0, Tclass._System.___hFunc1(TInt, TInt))
       && $IsAlloc(a#0_0, Tclass._System.___hFunc1(TInt, TInt), $Heap);
  var a#1_0: int;
  var ##c#1_0: ref;
  var ##y#1_0: int;
  var ##c#1_1: ref;
  var ##y#1_1: int;
  var ##c#1_2: ref;
  var ##y#1_2: int;
  var a#2_0: int;
  var ##c#2_0: ref;
  var ##y#2_0: int;
  var u#3_0: int;
  var ##c#3_0: ref;
  var ##y#3_0: int;
  var a#4_0: int;
  var ##y#4_0: int;
  var ##y#4_1: int;
  var ##y#4_2: int;
  var a#5_0: int;
  var ##y#5_0: int;
  var a#6_0: int;
  var ##y#6_0: int;

    // AddMethodImpl: Allocatedness_Function, Impl$$TwoStateAt.__default.Allocatedness__Function
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(374,34): initial state"} true;
    $_reverifyPost := false;
    $Heap_at_0 := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(376,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(376,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(5);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(376,24)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(376,24)"} true;

  after_0:
    $Heap_at_1 := $Heap;
    $Heap_at_2 := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(379,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, TwoStateAt.Cell.data) + 400;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(379,26)"} true;

  after_1:
    $Heap_at_3 := $Heap;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(382,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(384,15)
        assume true;
        assert c#0 != null;
        ##y#6_0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#6_0, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.Cell.Plus#canCall(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
        assume TwoStateAt.Cell.Plus#canCall(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
        a#6_0 := TwoStateAt.Cell.Plus(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(384,26)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(386,15)
        assume true;
        assert c#0 != null;
        ##y#5_0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#5_0, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
        assume TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
        a#5_0 := TwoStateAt.Cell.Plus(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(386,28)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(388,15)
        assume true;
        assert c#0 != null;
        ##y#4_0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#4_0, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_1);
        assume TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_1, $Heap, c#0, $Box(LitInt(0)));
        assert c#0 != null;
        ##y#4_1 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#4_1, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_2);
        assume TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_2, $Heap, c#0, $Box(LitInt(0)));
        assert c#0 != null;
        ##y#4_2 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#4_2, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_3);
        assume TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_3, $Heap, c#0, $Box(LitInt(0)));
        assume TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_1, $Heap, c#0, $Box(LitInt(0)))
           && TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_2, $Heap, c#0, $Box(LitInt(0)))
           && TwoStateAt.Cell.Plus#canCall(TInt, $Heap_at_3, $Heap, c#0, $Box(LitInt(0)));
        a#4_0 := TwoStateAt.Cell.Plus(TInt, $Heap_at_1, $Heap, c#0, $Box(LitInt(0)))
           + TwoStateAt.Cell.Plus(TInt, $Heap_at_2, $Heap, c#0, $Box(LitInt(0)))
           + TwoStateAt.Cell.Plus(TInt, $Heap_at_3, $Heap, c#0, $Box(LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(388,56)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(389,9)
        assume true;
        assert a#4_0 == LitInt(5 + 5 + 405 + 1215);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(391,15)
        assume true;
        ##c#3_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#3_0, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#3_0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#3_0, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.Cell.Sum#canCall(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
        assume TwoStateAt.Cell.Sum#canCall(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
        u#3_0 := TwoStateAt.Cell.Sum(TInt, old($Heap), $Heap, c#0, $Box(LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(391,31)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(393,15)
        assume true;
        ##c#2_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2_0, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#2_0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#2_0, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
        assume TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
        a#2_0 := TwoStateAt.Cell.Sum(TInt, $Heap_at_0, $Heap, c#0, $Box(LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(393,33)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(395,15)
        assume true;
        ##c#1_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1_0, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#1_0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#1_0, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_1);
        assume TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_1, $Heap, c#0, $Box(LitInt(0)));
        ##c#1_1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1_1, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#1_1 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#1_1, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_2);
        assume TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_2, $Heap, c#0, $Box(LitInt(0)));
        ##c#1_2 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1_2, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#1_2 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#1_2, TInt, $Heap);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_3);
        assume TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_3, $Heap, c#0, $Box(LitInt(0)));
        assume TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_1, $Heap, c#0, $Box(LitInt(0)))
           && TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_2, $Heap, c#0, $Box(LitInt(0)))
           && TwoStateAt.Cell.Sum#canCall(TInt, $Heap_at_3, $Heap, c#0, $Box(LitInt(0)));
        a#1_0 := TwoStateAt.Cell.Sum(TInt, $Heap_at_1, $Heap, c#0, $Box(LitInt(0)))
           + TwoStateAt.Cell.Sum(TInt, $Heap_at_2, $Heap, c#0, $Box(LitInt(0)))
           + TwoStateAt.Cell.Sum(TInt, $Heap_at_3, $Heap, c#0, $Box(LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(395,71)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(396,9)
        assume true;
        assert a#1_0 == LitInt(5 + 5 + 405 + 1215);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(398,15)
        assume true;
        assert 2 != $FunctionContextHeight;
        assert c#0 != null;
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume true;
        a#0_0 := TwoStateAt.Cell.Plus#Handle(TInt, old($Heap), c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(398,28)"} true;
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
        assume !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true);
        assert false;
    }

  after_3:
}



procedure CheckWellformed$$TwoStateAt.__default.Allocatedness__Lemma();
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.Allocatedness__Lemma();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.Allocatedness__Lemma() returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.Allocatedness__Lemma() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $Heap_at_0: Heap;
  var c#0: ref
     where $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var $Heap_at_1: Heap;
  var $Heap_at_2: Heap;
  var $rhs#0: int;
  var $Heap_at_3: Heap;
  var c##0_0: ref;
  var y##0_0: int;
  var c##0_1: ref;
  var y##0_1: int;
  var c##0_2: ref;
  var y##0_2: int;
  var c##1_0: ref;
  var y##1_0: int;
  var c##2_0: ref;
  var y##2_0: int;
  var y##3_0: int;
  var y##3_1: int;
  var y##3_2: int;
  var y##4_0: int;
  var y##5_0: int;

    // AddMethodImpl: Allocatedness_Lemma, Impl$$TwoStateAt.__default.Allocatedness__Lemma
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(402,31): initial state"} true;
    $_reverifyPost := false;
    $Heap_at_0 := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(404,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(404,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(5);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(404,24)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(404,24)"} true;

  after_0:
    $Heap_at_1 := $Heap;
    $Heap_at_2 := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(407,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, TwoStateAt.Cell.data];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, TwoStateAt.Cell.data) + 400;
    $Heap := update($Heap, c#0, TwoStateAt.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(407,26)"} true;

  after_1:
    $Heap_at_3 := $Heap;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(410,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(412,13)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert c#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##5_0 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.LL(old($Heap), $Heap, TInt, c#0, $Box(y##5_0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(412,15)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(414,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert c#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##4_0 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.LL($Heap_at_0, $Heap, TInt, c#0, $Box(y##4_0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(414,17)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(416,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert c#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##3_0 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_1);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.LL($Heap_at_1, $Heap, TInt, c#0, $Box(y##3_0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(416,17)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(417,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert c#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##3_1 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_2);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.LL($Heap_at_2, $Heap, TInt, c#0, $Box(y##3_1));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(417,17)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(418,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert c#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##3_2 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_3);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.LL($Heap_at_3, $Heap, TInt, c#0, $Box(y##3_2));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(418,17)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(420,27)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##2_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##2_0 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.IdentityLemma(old($Heap), $Heap, TInt, c##2_0, $Box(y##2_0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(420,32)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(422,29)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##1_0 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.IdentityLemma($Heap_at_0, $Heap, TInt, c##1_0, $Box(y##1_0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(422,34)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(424,29)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##0_0 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_1);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.IdentityLemma($Heap_at_1, $Heap, TInt, c##0_0, $Box(y##0_0));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(424,34)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(425,29)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_1 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##0_1 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_2);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.IdentityLemma($Heap_at_2, $Heap, TInt, c##0_1, $Box(y##0_1));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(425,34)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(426,29)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_2 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##0_2 := LitInt(0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_3);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$TwoStateAt.Cell.IdentityLemma($Heap_at_3, $Heap, TInt, c##0_2, $Box(y##0_2));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(426,34)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }

  after_3:
}



// function declaration for TwoStateAt._default.FuncMoreParams
function TwoStateAt.__default.FuncMoreParams($prevHeap: Heap, $heap: Heap, c#0: ref, d#0: ref) : int;

function TwoStateAt.__default.FuncMoreParams#canCall($prevHeap: Heap, $heap: Heap, c#0: ref, d#0: ref) : bool;

// frame axiom for TwoStateAt.__default.FuncMoreParams
axiom (forall $prevHeap: Heap, $h0: Heap, $h1: Heap, c#0: ref, d#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), TwoStateAt.__default.FuncMoreParams($prevHeap, $h1, c#0, d#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (TwoStateAt.__default.FuncMoreParams#canCall($prevHeap, $h0, c#0, d#0)
         || ($Is(c#0, Tclass.TwoStateAt.Cell()) && $Is(d#0, Tclass.TwoStateAt.Cell())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      false ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> TwoStateAt.__default.FuncMoreParams($prevHeap, $h0, c#0, d#0)
       == TwoStateAt.__default.FuncMoreParams($prevHeap, $h1, c#0, d#0));

// consequence axiom for TwoStateAt.__default.FuncMoreParams
axiom 27 <= $FunctionContextHeight
   ==> (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, d#0: ref :: 
    { TwoStateAt.__default.FuncMoreParams($prevHeap, $Heap, c#0, d#0) } 
    TwoStateAt.__default.FuncMoreParams#canCall($prevHeap, $Heap, c#0, d#0)
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell())
           && $Is(d#0, Tclass.TwoStateAt.Cell()))
       ==> true);

function TwoStateAt.__default.FuncMoreParams#requires(Heap, Heap, ref, ref) : bool;

// #requires axiom for TwoStateAt.__default.FuncMoreParams
axiom (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, d#0: ref :: 
  { TwoStateAt.__default.FuncMoreParams#requires($prevHeap, $Heap, c#0, d#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && $Is(c#0, Tclass.TwoStateAt.Cell())
       && $Is(d#0, Tclass.TwoStateAt.Cell())
     ==> TwoStateAt.__default.FuncMoreParams#requires($prevHeap, $Heap, c#0, d#0)
       == $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $prevHeap));

// definition axiom for TwoStateAt.__default.FuncMoreParams (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, d#0: ref :: 
    { TwoStateAt.__default.FuncMoreParams($prevHeap, $Heap, c#0, d#0), $IsGoodHeap($Heap) } 
    TwoStateAt.__default.FuncMoreParams#canCall($prevHeap, $Heap, c#0, d#0)
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell())
           && $Is(d#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.__default.FuncMoreParams($prevHeap, $Heap, c#0, d#0) == LitInt(7));

// definition axiom for TwoStateAt.__default.FuncMoreParams for all literals (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $prevHeap: Heap, $Heap: Heap, c#0: ref, d#0: ref :: 
    {:weight 3} { TwoStateAt.__default.FuncMoreParams($prevHeap, $Heap, Lit(c#0), Lit(d#0)), $IsGoodHeap($Heap) } 
    TwoStateAt.__default.FuncMoreParams#canCall($prevHeap, $Heap, Lit(c#0), Lit(d#0))
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && $Is(c#0, Tclass.TwoStateAt.Cell())
           && $Is(d#0, Tclass.TwoStateAt.Cell()))
       ==> TwoStateAt.__default.FuncMoreParams($prevHeap, $Heap, Lit(c#0), Lit(d#0))
         == LitInt(7));

procedure CheckWellformed$$TwoStateAt.__default.FuncMoreParams(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    d#0: ref
       where $Is(d#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(d#0, Tclass.TwoStateAt.Cell(), current$Heap));
  free requires 27 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



procedure CheckWellformed$$TwoStateAt.__default.LemmaMoreParams(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    d#0: ref
       where $Is(d#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(d#0, Tclass.TwoStateAt.Cell(), current$Heap))
   returns (e#0: ref
       where $Is(e#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(e#0, Tclass.TwoStateAt.Cell(), current$Heap));
  free requires 28 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.LemmaMoreParams(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    d#0: ref
       where $Is(d#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(d#0, Tclass.TwoStateAt.Cell(), current$Heap))
   returns (e#0: ref
       where $Is(e#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(e#0, Tclass.TwoStateAt.Cell(), current$Heap));
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$TwoStateAt.__default.LemmaMoreParams(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap), 
    d#0: ref
       where $Is(d#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(d#0, Tclass.TwoStateAt.Cell(), current$Heap))
   returns (defass#e#0: bool, 
    e#0: ref
       where defass#e#0
         ==> $Is(e#0, Tclass.TwoStateAt.Cell())
           && $IsAlloc(e#0, Tclass.TwoStateAt.Cell(), current$Heap), 
    $_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), previous$Heap);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$TwoStateAt.__default.LemmaMoreParams(previous$Heap: Heap, current$Heap: Heap, c#0: ref, d#0: ref)
   returns (defass#e#0: bool, e#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: LemmaMoreParams, Impl$$TwoStateAt.__default.LemmaMoreParams
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(431,73): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(432,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(433,9)
        assume true;
        assume true;
        e#0 := c#0;
        defass#e#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(433,12)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(435,9)
        assume true;
        assume true;
        e#0 := d#0;
        defass#e#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(435,12)"} true;
    }

    assert defass#e#0;
}



procedure CheckWellformed$$TwoStateAt.__default.TestFuncMoreParams(c0#0: ref
       where $Is(c0#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.TestFuncMoreParams(c0#0: ref
       where $Is(c0#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.TestFuncMoreParams(c0#0: ref
       where $Is(c0#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.TestFuncMoreParams(c0#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c1#0: ref
     where $Is(c1#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c1#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var $Heap_at_0: Heap;
  var c2#0: ref
     where $Is(c2#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c2#0, Tclass.TwoStateAt.Cell(), $Heap);
  var x##1: int;
  var x#0: int;
  var ##c#0_0: ref;
  var ##d#0_0: ref;
  var ##c#0_1: ref;
  var ##d#0_1: ref;
  var ##c#1_0: ref;
  var ##d#1_0: ref;
  var ##c#1_1: ref;
  var ##d#1_1: ref;
  var ##c#1_2: ref;
  var ##d#1_2: ref;
  var ##c#2_0: ref;
  var ##d#2_0: ref;
  var ##c#2_1: ref;
  var ##d#2_1: ref;

    // AddMethodImpl: TestFuncMoreParams, Impl$$TwoStateAt.__default.TestFuncMoreParams
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(438,38): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(439,12)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(439,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(1);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(439,25)"} true;
    c1#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(439,25)"} true;
    $Heap_at_0 := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(441,12)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(441,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(2);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(441,25)"} true;
    c2#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(441,25)"} true;

  after_0:
    havoc x#0;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(444,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(446,11)
        assume true;
        ##c#2_0 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2_0, Tclass.TwoStateAt.Cell(), $Heap);
        ##d#2_0 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#2_0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c0#0, c0#0);
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c0#0, c0#0);
        x#0 := TwoStateAt.__default.FuncMoreParams(old($Heap), $Heap, c0#0, c0#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(446,35)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(447,11)
        assume true;
        ##c#2_1 := c1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2_1, Tclass.TwoStateAt.Cell(), $Heap);
        ##d#2_1 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#2_1, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(c1#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c1#0, c0#0);
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c1#0, c0#0);
        x#0 := TwoStateAt.__default.FuncMoreParams(old($Heap), $Heap, c1#0, c0#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(447,35)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(449,11)
        assume true;
        ##c#1_0 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1_0, Tclass.TwoStateAt.Cell(), $Heap);
        ##d#1_0 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1_0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.__default.FuncMoreParams#canCall($Heap_at_0, $Heap, c0#0, c0#0);
        assume TwoStateAt.__default.FuncMoreParams#canCall($Heap_at_0, $Heap, c0#0, c0#0);
        x#0 := TwoStateAt.__default.FuncMoreParams($Heap_at_0, $Heap, c0#0, c0#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(449,37)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(450,11)
        assume true;
        ##c#1_1 := c1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1_1, Tclass.TwoStateAt.Cell(), $Heap);
        ##d#1_1 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1_1, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(c1#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.__default.FuncMoreParams#canCall($Heap_at_0, $Heap, c1#0, c0#0);
        assume TwoStateAt.__default.FuncMoreParams#canCall($Heap_at_0, $Heap, c1#0, c0#0);
        x#0 := TwoStateAt.__default.FuncMoreParams($Heap_at_0, $Heap, c1#0, c0#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(450,37)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(451,11)
        assume true;
        ##c#1_2 := c2#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1_2, Tclass.TwoStateAt.Cell(), $Heap);
        ##d#1_2 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1_2, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(c2#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.__default.FuncMoreParams#canCall($Heap_at_0, $Heap, c2#0, c0#0);
        assume TwoStateAt.__default.FuncMoreParams#canCall($Heap_at_0, $Heap, c2#0, c0#0);
        x#0 := TwoStateAt.__default.FuncMoreParams($Heap_at_0, $Heap, c2#0, c0#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(451,37)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(453,11)
        assume true;
        ##c#0_0 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_0, Tclass.TwoStateAt.Cell(), $Heap);
        ##d#0_0 := c1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0_0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c0#0, c1#0);
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c0#0, c1#0);
        x#0 := TwoStateAt.__default.FuncMoreParams(old($Heap), $Heap, c0#0, c1#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(453,35)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(454,11)
        assume true;
        ##c#0_1 := c0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_1, Tclass.TwoStateAt.Cell(), $Heap);
        ##d#0_1 := c2#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0_1, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c0#0, c2#0);
        assume TwoStateAt.__default.FuncMoreParams#canCall(old($Heap), $Heap, c0#0, c2#0);
        x#0 := TwoStateAt.__default.FuncMoreParams(old($Heap), $Heap, c0#0, c2#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(454,35)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$TwoStateAt.__default.TestLemmaMoreParams(c0#0: ref
       where $Is(c0#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.TestLemmaMoreParams(c0#0: ref
       where $Is(c0#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.TestLemmaMoreParams(c0#0: ref
       where $Is(c0#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.TestLemmaMoreParams(c0#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c1#0: ref
     where $Is(c1#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c1#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var $Heap_at_0: Heap;
  var c2#0: ref
     where $Is(c2#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c2#0, Tclass.TwoStateAt.Cell(), $Heap);
  var x##1: int;
  var defass#x#0: bool;
  var x#0: ref
     where defass#x#0
       ==> $Is(x#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(x#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $rhs##0_0: ref
     where $Is($rhs##0_0, Tclass.TwoStateAt.Cell())
       && $IsAlloc($rhs##0_0, Tclass.TwoStateAt.Cell(), $Heap);
  var c##0_0: ref;
  var d##0_0: ref;
  var $rhs##0_1: ref
     where $Is($rhs##0_1, Tclass.TwoStateAt.Cell())
       && $IsAlloc($rhs##0_1, Tclass.TwoStateAt.Cell(), $Heap);
  var c##0_1: ref;
  var d##0_1: ref;
  var $rhs##1_0: ref
     where $Is($rhs##1_0, Tclass.TwoStateAt.Cell())
       && $IsAlloc($rhs##1_0, Tclass.TwoStateAt.Cell(), $Heap);
  var c##1_0: ref;
  var d##1_0: ref;
  var $rhs##1_1: ref
     where $Is($rhs##1_1, Tclass.TwoStateAt.Cell())
       && $IsAlloc($rhs##1_1, Tclass.TwoStateAt.Cell(), $Heap);
  var c##1_1: ref;
  var d##1_1: ref;
  var $rhs##1_2: ref
     where $Is($rhs##1_2, Tclass.TwoStateAt.Cell())
       && $IsAlloc($rhs##1_2, Tclass.TwoStateAt.Cell(), $Heap);
  var c##1_2: ref;
  var d##1_2: ref;
  var $rhs##2_0: ref
     where $Is($rhs##2_0, Tclass.TwoStateAt.Cell())
       && $IsAlloc($rhs##2_0, Tclass.TwoStateAt.Cell(), $Heap);
  var c##2_0: ref;
  var d##2_0: ref;
  var $rhs##2_1: ref
     where $Is($rhs##2_1, Tclass.TwoStateAt.Cell())
       && $IsAlloc($rhs##2_1, Tclass.TwoStateAt.Cell(), $Heap);
  var c##2_1: ref;
  var d##2_1: ref;

    // AddMethodImpl: TestLemmaMoreParams, Impl$$TwoStateAt.__default.TestLemmaMoreParams
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(457,39): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(458,12)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(458,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(1);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(458,25)"} true;
    c1#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(458,25)"} true;
    $Heap_at_0 := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(460,12)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(460,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(2);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(460,25)"} true;
    c2#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(460,25)"} true;

  after_0:
    havoc x#0 /* where defass#x#0
       ==> $Is(x#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(x#0, Tclass.TwoStateAt.Cell(), $Heap) */;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(463,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(465,29)
        assume true;
        // TrCallStmt: Adding lhs with type Cell
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##2_0 := c0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##2_0 := c0#0;
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##2_0 := Call$$TwoStateAt.__default.LemmaMoreParams(old($Heap), $Heap, c##2_0, d##2_0);
        // TrCallStmt: After ProcessCallStmt
        x#0 := $rhs##2_0;
        defass#x#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(465,36)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(466,29)
        assume true;
        // TrCallStmt: Adding lhs with type Cell
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##2_1 := c1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##2_1 := c0#0;
        assert $IsAlloc(c1#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##2_1 := Call$$TwoStateAt.__default.LemmaMoreParams(old($Heap), $Heap, c##2_1, d##2_1);
        // TrCallStmt: After ProcessCallStmt
        x#0 := $rhs##2_1;
        defass#x#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(466,36)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(468,31)
        assume true;
        // TrCallStmt: Adding lhs with type Cell
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_0 := c0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##1_0 := c0#0;
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1_0 := Call$$TwoStateAt.__default.LemmaMoreParams($Heap_at_0, $Heap, c##1_0, d##1_0);
        // TrCallStmt: After ProcessCallStmt
        x#0 := $rhs##1_0;
        defass#x#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(468,38)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(469,31)
        assume true;
        // TrCallStmt: Adding lhs with type Cell
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_1 := c1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##1_1 := c0#0;
        assert $IsAlloc(c1#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1_1 := Call$$TwoStateAt.__default.LemmaMoreParams($Heap_at_0, $Heap, c##1_1, d##1_1);
        // TrCallStmt: After ProcessCallStmt
        x#0 := $rhs##1_1;
        defass#x#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(469,38)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(470,31)
        assume true;
        // TrCallStmt: Adding lhs with type Cell
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_2 := c2#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##1_2 := c0#0;
        assert $IsAlloc(c2#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1_2 := Call$$TwoStateAt.__default.LemmaMoreParams($Heap_at_0, $Heap, c##1_2, d##1_2);
        // TrCallStmt: After ProcessCallStmt
        x#0 := $rhs##1_2;
        defass#x#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(470,38)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(472,29)
        assume true;
        // TrCallStmt: Adding lhs with type Cell
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0_0 := c1#0;
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$TwoStateAt.__default.LemmaMoreParams(old($Heap), $Heap, c##0_0, d##0_0);
        // TrCallStmt: After ProcessCallStmt
        x#0 := $rhs##0_0;
        defass#x#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(472,36)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(473,29)
        assume true;
        // TrCallStmt: Adding lhs with type Cell
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_1 := c0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0_1 := c2#0;
        assert $IsAlloc(c0#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_1 := Call$$TwoStateAt.__default.LemmaMoreParams(old($Heap), $Heap, c##0_1, d##0_1);
        // TrCallStmt: After ProcessCallStmt
        x#0 := $rhs##0_1;
        defass#x#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(473,36)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$TwoStateAt.__default.TestOthers0(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.TestOthers0(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.TestOthers0(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.TestOthers0(dt#0: DatatypeType, 
    nt#0: int, 
    ot#0: Box, 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var $Heap_at_0: Heap;
  var n#0: int where LitInt(0) <= n#0;
  var x#0: int;
  var y#0: int;
  var ##x#0_0: real;
  var ##y#0_0: DatatypeType;
  var ##c#0_0: ref;
  var ##x#0_1: real;
  var ##y#0_1: DatatypeType;
  var ##c#0_1: ref;
  var $rhs##1_0: int where LitInt(0) <= $rhs##1_0;
  var x##1_0: real;
  var y##1_0: DatatypeType;
  var c##1_0: ref;
  var $rhs##1_1: int where LitInt(0) <= $rhs##1_1;
  var x##1_1: real;
  var y##1_1: DatatypeType;
  var c##1_1: ref;
  var ##x#2_0: real;
  var ##y#2_0: DatatypeType;
  var ##c#2_0: ref;
  var ##x#2_1: real;
  var ##y#2_1: DatatypeType;
  var ##c#2_1: ref;
  var $rhs##3_0: int where LitInt(0) <= $rhs##3_0;
  var x##3_0: real;
  var y##3_0: DatatypeType;
  var c##3_0: ref;
  var $rhs##3_1: int where LitInt(0) <= $rhs##3_1;
  var x##3_1: real;
  var y##3_1: DatatypeType;
  var c##3_1: ref;

    // AddMethodImpl: TestOthers0, Impl$$TwoStateAt.__default.TestOthers0
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(551,82): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(552,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(552,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(333);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(552,26)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(552,26)"} true;
    $Heap_at_0 := $Heap;
    havoc n#0 /* where LitInt(0) <= n#0 */, x#0, y#0;

  after_0:
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(556,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(557,9)
        assume true;
        ##x#0_0 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_0, TReal, $Heap);
        ##y#0_0 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_0, Tclass._System.Tuple0(), $Heap);
        ##c#0_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap_at_0);
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.DT.F#canCall(TReal, 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume TwoStateAt.DT.F#canCall(TReal, 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        x#0 := TwoStateAt.DT.F(TReal, 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(557,30)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(558,9)
        assume true;
        ##x#0_1 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_1, TReal, $Heap);
        ##y#0_1 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_1, Tclass._System.Tuple0(), $Heap);
        ##c#0_1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_1, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), old($Heap));
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.DT.F#canCall(TReal, 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume TwoStateAt.DT.F#canCall(TReal, 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        x#0 := TwoStateAt.DT.F(TReal, 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(558,24)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(559,12)
        if (*)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(560,22)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_0 := r#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_0 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_0 := c#0;
            assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap_at_0);
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_0 := Call$$TwoStateAt.DT.L($Heap_at_0, $Heap, TReal, Tclass._System.Tuple0(), dt#0, $Box(x##1_0), $Box(y##1_0), c##1_0);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(560,30)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(561,16)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_1 := r#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_1 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_1 := c#0;
            assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), old($Heap));
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_1 := Call$$TwoStateAt.DT.L(old($Heap), $Heap, TReal, Tclass._System.Tuple0(), dt#0, $Box(x##1_1), $Box(y##1_1), c##1_1);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(561,24)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(562,12)
            if (*)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(563,9)
                assume true;
                ##x#2_0 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#2_0, TReal, $Heap);
                ##y#2_0 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#2_0, Tclass._System.Tuple0(), $Heap);
                ##c#2_0 := c#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2_0, Tclass.TwoStateAt.Cell(), $Heap);
                assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
                assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
                assume TwoStateAt.DT.G#canCall(TReal, Tclass._System.Tuple0(), $Heap_at_0, $Heap, $Box(r#0), $Box(u#0), c#0);
                assume TwoStateAt.DT.G#canCall(TReal, Tclass._System.Tuple0(), $Heap_at_0, $Heap, $Box(r#0), $Box(u#0), c#0);
                y#0 := TwoStateAt.DT.G(TReal, Tclass._System.Tuple0(), $Heap_at_0, $Heap, $Box(r#0), $Box(u#0), c#0);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(563,30)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(564,9)
                assume true;
                ##x#2_1 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#2_1, TReal, $Heap);
                ##y#2_1 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#2_1, Tclass._System.Tuple0(), $Heap);
                ##c#2_1 := c#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2_1, Tclass.TwoStateAt.Cell(), $Heap);
                assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
                assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
                assume TwoStateAt.DT.G#canCall(TReal, Tclass._System.Tuple0(), old($Heap), $Heap, $Box(r#0), $Box(u#0), c#0);
                assume TwoStateAt.DT.G#canCall(TReal, Tclass._System.Tuple0(), old($Heap), $Heap, $Box(r#0), $Box(u#0), c#0);
                y#0 := TwoStateAt.DT.G(TReal, Tclass._System.Tuple0(), old($Heap), $Heap, $Box(r#0), $Box(u#0), c#0);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(564,24)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(565,12)
                if (*)
                {
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(566,22)
                    assume true;
                    // TrCallStmt: Adding lhs with type nat
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    x##3_0 := r#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    y##3_0 := u#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c##3_0 := c#0;
                    assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
                    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call $rhs##3_0 := Call$$TwoStateAt.DT.M($Heap_at_0, $Heap, TReal, Tclass._System.Tuple0(), $Box(x##3_0), $Box(y##3_0), c##3_0);
                    // TrCallStmt: After ProcessCallStmt
                    n#0 := $rhs##3_0;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(566,30)"} true;
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(567,16)
                    assume true;
                    // TrCallStmt: Adding lhs with type nat
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    x##3_1 := r#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    y##3_1 := u#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c##3_1 := c#0;
                    assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
                    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call $rhs##3_1 := Call$$TwoStateAt.DT.M(old($Heap), $Heap, TReal, Tclass._System.Tuple0(), $Box(x##3_1), $Box(y##3_1), c##3_1);
                    // TrCallStmt: After ProcessCallStmt
                    n#0 := $rhs##3_1;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(567,24)"} true;
                }
                else
                {
                }
            }
        }
    }
}



procedure CheckWellformed$$TwoStateAt.__default.TestOthers1(nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.TestOthers1(nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.TestOthers1(nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0), 
    c#0: ref
       where $Is(c#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.TestOthers1(nt#0: int, ot#0: Box, r#0: ref, t#0: bv19, u#0: DatatypeType, c#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var dtx#0: ref
     where $Is(dtx#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(dtx#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var dt#0: DatatypeType
     where $Is(dt#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
       && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap);
  var $Heap_at_0: Heap;
  var n#0: int where LitInt(0) <= n#0;
  var x#0: int;
  var ##x#0_0: ref;
  var ##y#0_0: DatatypeType;
  var ##c#0_0: ref;
  var ##x#0_1: ref;
  var ##y#0_1: DatatypeType;
  var ##c#0_1: ref;
  var $rhs##1_0: int where LitInt(0) <= $rhs##1_0;
  var x##1_0: ref;
  var y##1_0: DatatypeType;
  var c##1_0: ref;
  var $rhs##1_1: int where LitInt(0) <= $rhs##1_1;
  var x##1_1: ref;
  var y##1_1: DatatypeType;
  var c##1_1: ref;

    // AddMethodImpl: TestOthers1, Impl$$TwoStateAt.__default.TestOthers1
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(571,77): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(572,13)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(572,16)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(333);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(572,28)"} true;
    dtx#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(572,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(573,12)
    assume true;
    assume true;
    dt#0 := #TwoStateAt.DT.Blue($Box(dtx#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(573,23)"} true;
    $Heap_at_0 := $Heap;
    havoc n#0 /* where LitInt(0) <= n#0 */, x#0;

  after_0:
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(577,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(578,9)
        assume true;
        ##x#0_0 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_0, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#0_0 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_0, Tclass._System.Tuple0(), $Heap);
        ##c#0_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap_at_0);
        assert $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.DT.F#canCall(Tclass.TwoStateAt.Cell(), 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume TwoStateAt.DT.F#canCall(Tclass.TwoStateAt.Cell(), 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        x#0 := TwoStateAt.DT.F(Tclass.TwoStateAt.Cell(), 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(578,30)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(579,9)
        assume true;
        ##x#0_1 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_1, Tclass.TwoStateAt.Cell(), $Heap);
        ##y#0_1 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_1, Tclass._System.Tuple0(), $Heap);
        ##c#0_1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_1, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), old($Heap));
        assert $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.DT.F#canCall(Tclass.TwoStateAt.Cell(), 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume TwoStateAt.DT.F#canCall(Tclass.TwoStateAt.Cell(), 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        x#0 := TwoStateAt.DT.F(Tclass.TwoStateAt.Cell(), 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          dt#0, 
          $Box(r#0), 
          $Box(u#0), 
          c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(579,24)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(580,12)
        if (*)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(581,22)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_0 := r#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_0 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_0 := c#0;
            assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap_at_0);
            assert $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_0 := Call$$TwoStateAt.DT.L($Heap_at_0, $Heap, Tclass.TwoStateAt.Cell(), Tclass._System.Tuple0(), dt#0, $Box(x##1_0), $Box(y##1_0), c##1_0);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(581,30)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(582,16)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_1 := r#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_1 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_1 := c#0;
            assert $IsAlloc(dt#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), old($Heap));
            assert $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), old($Heap));
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_1 := Call$$TwoStateAt.DT.L(old($Heap), $Heap, Tclass.TwoStateAt.Cell(), Tclass._System.Tuple0(), dt#0, $Box(x##1_1), $Box(y##1_1), c##1_1);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(582,24)"} true;
        }
        else
        {
        }
    }
}



procedure CheckWellformed$$TwoStateAt.__default.TestOthers2(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.TestOthers2(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.TestOthers2(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.TestOthers2(dt#0: DatatypeType, 
    nt#0: int, 
    ot#0: Box, 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var $Heap_at_0: Heap;
  var n#0: int where LitInt(0) <= n#0;
  var x#0: int;
  var y#0: int;
  var ##y#0_0: DatatypeType;
  var ##c#0_0: ref;
  var ##y#0_1: DatatypeType;
  var ##c#0_1: ref;
  var $rhs##1_0: int where LitInt(0) <= $rhs##1_0;
  var y##1_0: DatatypeType;
  var c##1_0: ref;
  var $rhs##1_1: int where LitInt(0) <= $rhs##1_1;
  var y##1_1: DatatypeType;
  var c##1_1: ref;
  var ##y#2_0: DatatypeType;
  var ##c#2_0: ref;
  var ##y#2_1: DatatypeType;
  var ##c#2_1: ref;
  var $rhs##3_0: int where LitInt(0) <= $rhs##3_0;
  var y##3_0: DatatypeType;
  var c##3_0: ref;
  var $rhs##3_1: int where LitInt(0) <= $rhs##3_1;
  var y##3_1: DatatypeType;
  var c##3_1: ref;

    // AddMethodImpl: TestOthers2, Impl$$TwoStateAt.__default.TestOthers2
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(586,82): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(587,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(587,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(333);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(587,26)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(587,26)"} true;
    $Heap_at_0 := $Heap;
    havoc n#0 /* where LitInt(0) <= n#0 */, x#0, y#0;

  after_0:
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(591,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(592,9)
        assume true;
        ##y#0_0 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_0, Tclass._System.Tuple0(), $Heap);
        ##c#0_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.NT.F#canCall(Tclass._System.Tuple0(), $Heap_at_0, $Heap, nt#0, $Box(u#0), c#0);
        assume TwoStateAt.NT.F#canCall(Tclass._System.Tuple0(), $Heap_at_0, $Heap, nt#0, $Box(u#0), c#0);
        x#0 := TwoStateAt.NT.F(Tclass._System.Tuple0(), $Heap_at_0, $Heap, nt#0, $Box(u#0), c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(592,27)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(593,9)
        assume true;
        ##y#0_1 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_1, Tclass._System.Tuple0(), $Heap);
        ##c#0_1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_1, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.NT.F#canCall(Tclass._System.Tuple0(), old($Heap), $Heap, nt#0, $Box(u#0), c#0);
        assume TwoStateAt.NT.F#canCall(Tclass._System.Tuple0(), old($Heap), $Heap, nt#0, $Box(u#0), c#0);
        x#0 := TwoStateAt.NT.F(Tclass._System.Tuple0(), old($Heap), $Heap, nt#0, $Box(u#0), c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(593,21)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(594,12)
        if (*)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(595,22)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_0 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_0 := c#0;
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_0 := Call$$TwoStateAt.NT.L($Heap_at_0, $Heap, Tclass._System.Tuple0(), nt#0, $Box(y##1_0), c##1_0);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(595,27)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(596,16)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_1 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_1 := c#0;
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_1 := Call$$TwoStateAt.NT.L(old($Heap), $Heap, Tclass._System.Tuple0(), nt#0, $Box(y##1_1), c##1_1);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(596,21)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(597,12)
            if (*)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(598,9)
                assume true;
                ##y#2_0 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#2_0, Tclass._System.Tuple0(), $Heap);
                ##c#2_0 := c#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2_0, Tclass.TwoStateAt.Cell(), $Heap);
                assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
                assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
                assume TwoStateAt.NT.G#canCall(Tclass._System.Tuple0(), $Heap_at_0, $Heap, $Box(u#0), c#0);
                assume TwoStateAt.NT.G#canCall(Tclass._System.Tuple0(), $Heap_at_0, $Heap, $Box(u#0), c#0);
                y#0 := TwoStateAt.NT.G(Tclass._System.Tuple0(), $Heap_at_0, $Heap, $Box(u#0), c#0);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(598,27)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(599,9)
                assume true;
                ##y#2_1 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#2_1, Tclass._System.Tuple0(), $Heap);
                ##c#2_1 := c#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2_1, Tclass.TwoStateAt.Cell(), $Heap);
                assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
                assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
                assume TwoStateAt.NT.G#canCall(Tclass._System.Tuple0(), old($Heap), $Heap, $Box(u#0), c#0);
                assume TwoStateAt.NT.G#canCall(Tclass._System.Tuple0(), old($Heap), $Heap, $Box(u#0), c#0);
                y#0 := TwoStateAt.NT.G(Tclass._System.Tuple0(), old($Heap), $Heap, $Box(u#0), c#0);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(599,21)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(600,12)
                if (*)
                {
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(601,22)
                    assume true;
                    // TrCallStmt: Adding lhs with type nat
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    y##3_0 := u#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c##3_0 := c#0;
                    assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
                    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call $rhs##3_0 := Call$$TwoStateAt.NT.M($Heap_at_0, $Heap, Tclass._System.Tuple0(), $Box(y##3_0), c##3_0);
                    // TrCallStmt: After ProcessCallStmt
                    n#0 := $rhs##3_0;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(601,27)"} true;
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(602,16)
                    assume true;
                    // TrCallStmt: Adding lhs with type nat
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    y##3_1 := u#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c##3_1 := c#0;
                    assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
                    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call $rhs##3_1 := Call$$TwoStateAt.NT.M(old($Heap), $Heap, Tclass._System.Tuple0(), $Box(y##3_1), c##3_1);
                    // TrCallStmt: After ProcessCallStmt
                    n#0 := $rhs##3_1;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(602,21)"} true;
                }
                else
                {
                }
            }
        }
    }
}



procedure CheckWellformed$$TwoStateAt.__default.TestOthers3(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.TestOthers3(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.TestOthers3(dt#0: DatatypeType
       where $Is(dt#0, Tclass.TwoStateAt.DT(TReal))
         && $IsAlloc(dt#0, Tclass.TwoStateAt.DT(TReal), $Heap)
         && $IsA#TwoStateAt.DT(dt#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(TBitvector(19)))
         && $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap), 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0))
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.TestOthers3(dt#0: DatatypeType, 
    nt#0: int, 
    ot#0: Box, 
    r#0: real, 
    t#0: bv19, 
    u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var $Heap_at_0: Heap;
  var n#0: int where LitInt(0) <= n#0;
  var x#0: int;
  var y#0: int;
  var ##x#0_0: bv19;
  var ##y#0_0: DatatypeType;
  var ##c#0_0: ref;
  var ##x#0_1: bv19;
  var ##y#0_1: DatatypeType;
  var ##c#0_1: ref;
  var $rhs##1_0: int where LitInt(0) <= $rhs##1_0;
  var x##1_0: bv19;
  var y##1_0: DatatypeType;
  var c##1_0: ref;
  var $rhs##1_1: int where LitInt(0) <= $rhs##1_1;
  var x##1_1: bv19;
  var y##1_1: DatatypeType;
  var c##1_1: ref;
  var ##ot#2_0: Box;
  var ##x#2_0: bv19;
  var ##y#2_0: DatatypeType;
  var ##c#2_0: ref;
  var ##ot#2_1: Box;
  var ##x#2_1: bv19;
  var ##y#2_1: DatatypeType;
  var ##c#2_1: ref;
  var $rhs##3_0: int where LitInt(0) <= $rhs##3_0;
  var ot##3_0: Box;
  var x##3_0: bv19;
  var y##3_0: DatatypeType;
  var c##3_0: ref;
  var $rhs##3_1: int where LitInt(0) <= $rhs##3_1;
  var ot##3_1: Box;
  var x##3_1: bv19;
  var y##3_1: DatatypeType;
  var c##3_1: ref;

    // AddMethodImpl: TestOthers3, Impl$$TwoStateAt.__default.TestOthers3
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(606,82): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(607,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(607,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(333);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(607,26)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(607,26)"} true;
    $Heap_at_0 := $Heap;
    havoc n#0 /* where LitInt(0) <= n#0 */, x#0, y#0;

  after_0:
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(611,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(612,9)
        assume true;
        ##x#0_0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_0, TBitvector(19), $Heap);
        ##y#0_0 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_0, Tclass._System.Tuple0(), $Heap);
        ##c#0_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_0, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap_at_0);
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
        assume TwoStateAt.OT.F#canCall(TBitvector(19), 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          ot#0, 
          $Box(t#0), 
          $Box(u#0), 
          c#0);
        assume TwoStateAt.OT.F#canCall(TBitvector(19), 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          ot#0, 
          $Box(t#0), 
          $Box(u#0), 
          c#0);
        x#0 := TwoStateAt.OT.F(TBitvector(19), 
          Tclass._System.Tuple0(), 
          $Heap_at_0, 
          $Heap, 
          ot#0, 
          $Box(t#0), 
          $Box(u#0), 
          c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(612,30)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(613,9)
        assume true;
        ##x#0_1 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_1, TBitvector(19), $Heap);
        ##y#0_1 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_1, Tclass._System.Tuple0(), $Heap);
        ##c#0_1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_1, Tclass.TwoStateAt.Cell(), $Heap);
        assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), old($Heap));
        assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
        assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
        assume TwoStateAt.OT.F#canCall(TBitvector(19), 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          ot#0, 
          $Box(t#0), 
          $Box(u#0), 
          c#0);
        assume TwoStateAt.OT.F#canCall(TBitvector(19), 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          ot#0, 
          $Box(t#0), 
          $Box(u#0), 
          c#0);
        x#0 := TwoStateAt.OT.F(TBitvector(19), 
          Tclass._System.Tuple0(), 
          old($Heap), 
          $Heap, 
          ot#0, 
          $Box(t#0), 
          $Box(u#0), 
          c#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(613,24)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(614,12)
        if (*)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(615,22)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_0 := t#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_0 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_0 := c#0;
            assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap_at_0);
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_0 := Call$$TwoStateAt.OT.L($Heap_at_0, $Heap, TBitvector(19), Tclass._System.Tuple0(), ot#0, $Box(x##1_0), $Box(y##1_0), c##1_0);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(615,30)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(616,16)
            assume true;
            // TrCallStmt: Adding lhs with type nat
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_1 := t#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##1_1 := u#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_1 := c#0;
            assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), old($Heap));
            assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
            assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_1 := Call$$TwoStateAt.OT.L(old($Heap), $Heap, TBitvector(19), Tclass._System.Tuple0(), ot#0, $Box(x##1_1), $Box(y##1_1), c##1_1);
            // TrCallStmt: After ProcessCallStmt
            n#0 := $rhs##1_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(616,24)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(617,12)
            if (*)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(618,9)
                assume true;
                ##ot#2_0 := ot#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##ot#2_0, #$OT(TBitvector(19)), $Heap);
                ##x#2_0 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#2_0, TBitvector(19), $Heap);
                ##y#2_0 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#2_0, Tclass._System.Tuple0(), $Heap);
                ##c#2_0 := c#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2_0, Tclass.TwoStateAt.Cell(), $Heap);
                assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap_at_0);
                assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
                assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
                assume TwoStateAt.OT.G#canCall(TBitvector(19), 
                  Tclass._System.Tuple0(), 
                  $Heap_at_0, 
                  $Heap, 
                  ot#0, 
                  $Box(t#0), 
                  $Box(u#0), 
                  c#0);
                assume TwoStateAt.OT.G#canCall(TBitvector(19), 
                  Tclass._System.Tuple0(), 
                  $Heap_at_0, 
                  $Heap, 
                  ot#0, 
                  $Box(t#0), 
                  $Box(u#0), 
                  c#0);
                y#0 := TwoStateAt.OT.G(TBitvector(19), 
                  Tclass._System.Tuple0(), 
                  $Heap_at_0, 
                  $Heap, 
                  ot#0, 
                  $Box(t#0), 
                  $Box(u#0), 
                  c#0);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(618,34)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(619,9)
                assume true;
                ##ot#2_1 := ot#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##ot#2_1, #$OT(TBitvector(19)), $Heap);
                ##x#2_1 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#2_1, TBitvector(19), $Heap);
                ##y#2_1 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#2_1, Tclass._System.Tuple0(), $Heap);
                ##c#2_1 := c#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2_1, Tclass.TwoStateAt.Cell(), $Heap);
                assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), old($Heap));
                assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
                assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
                assume TwoStateAt.OT.G#canCall(TBitvector(19), 
                  Tclass._System.Tuple0(), 
                  old($Heap), 
                  $Heap, 
                  ot#0, 
                  $Box(t#0), 
                  $Box(u#0), 
                  c#0);
                assume TwoStateAt.OT.G#canCall(TBitvector(19), 
                  Tclass._System.Tuple0(), 
                  old($Heap), 
                  $Heap, 
                  ot#0, 
                  $Box(t#0), 
                  $Box(u#0), 
                  c#0);
                y#0 := TwoStateAt.OT.G(TBitvector(19), 
                  Tclass._System.Tuple0(), 
                  old($Heap), 
                  $Heap, 
                  ot#0, 
                  $Box(t#0), 
                  $Box(u#0), 
                  c#0);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(619,28)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(620,12)
                if (*)
                {
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(621,22)
                    assume true;
                    // TrCallStmt: Adding lhs with type nat
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    ot##3_0 := ot#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    x##3_0 := t#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    y##3_0 := u#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c##3_0 := c#0;
                    assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), $Heap_at_0);
                    assert $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap_at_0);
                    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap_at_0);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call $rhs##3_0 := Call$$TwoStateAt.OT.M($Heap_at_0, $Heap, TBitvector(19), Tclass._System.Tuple0(), ot##3_0, $Box(x##3_0), $Box(y##3_0), c##3_0);
                    // TrCallStmt: After ProcessCallStmt
                    n#0 := $rhs##3_0;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(621,34)"} true;
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(622,16)
                    assume true;
                    // TrCallStmt: Adding lhs with type nat
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    ot##3_1 := ot#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    x##3_1 := t#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    y##3_1 := u#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c##3_1 := c#0;
                    assert $IsAllocBox(ot#0, #$OT(TBitvector(19)), old($Heap));
                    assert $IsAlloc(u#0, Tclass._System.Tuple0(), old($Heap));
                    assert $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), old($Heap));
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call $rhs##3_1 := Call$$TwoStateAt.OT.M(old($Heap), $Heap, TBitvector(19), Tclass._System.Tuple0(), ot##3_1, $Box(x##3_1), $Box(y##3_1), c##3_1);
                    // TrCallStmt: After ProcessCallStmt
                    n#0 := $rhs##3_1;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(622,28)"} true;
                }
                else
                {
                }
            }
        }
    }
}



procedure CheckWellformed$$TwoStateAt.__default.TestOthers4(d0#0: DatatypeType
       where $Is(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
         && $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap)
         && $IsA#TwoStateAt.DT(d0#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()))
         && $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.TestOthers4(d0#0: DatatypeType
       where $Is(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
         && $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap)
         && $IsA#TwoStateAt.DT(d0#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()))
         && $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.TestOthers4(d0#0: DatatypeType
       where $Is(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
         && $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap)
         && $IsA#TwoStateAt.DT(d0#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()))
         && $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function TwoStateAt.DT.F#Handle(Ty, Ty, Heap, DatatypeType) : HandleType;

axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: DatatypeType, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Apply3(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.F#Handle(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  Apply3(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.F#Handle(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == $Box(TwoStateAt.DT.F(TwoStateAt.DT$X, 
        TwoStateAt.DT.F$Y, 
        $prevHeap, 
        $heap, 
        $self, 
        $fh$0x#0, 
        $fh$0x#1, 
        $Unbox($fh$0x#2): ref)));

axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: DatatypeType, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Requires3(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.F#Handle(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  Requires3(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.F#Handle(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == TwoStateAt.DT.F#requires(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      $prevHeap, 
      $heap, 
      $self, 
      $fh$0x#0, 
      $fh$0x#1, 
      $Unbox($fh$0x#2): ref));

axiom (forall $bx: Box, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: DatatypeType, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Reads3(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.F#Handle(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)[$bx] } 
  Reads3(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.F#Handle(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)[$bx]
     == 
    ($Unbox($bx): ref
     == $Unbox($fh$0x#2): ref));

axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: DatatypeType, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: ref :: 
  { TwoStateAt.DT.F(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      $prevHeap, 
      $heap, 
      $self, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  TwoStateAt.DT.F(TwoStateAt.DT$X, 
      TwoStateAt.DT.F$Y, 
      $prevHeap, 
      $heap, 
      $self, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == $Unbox(Apply3(TwoStateAt.DT$X, 
        TwoStateAt.DT.F$Y, 
        Tclass.TwoStateAt.Cell(), 
        TInt, 
        $heap, 
        TwoStateAt.DT.F#Handle(TwoStateAt.DT$X, TwoStateAt.DT.F$Y, $prevHeap, $self), 
        $fh$0x#0, 
        $fh$0x#1, 
        $Box($fh$0x#2))): int);

function TwoStateAt.NT.F#Handle(Ty, Heap, int) : HandleType;

axiom (forall TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: int, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box :: 
  { Apply2(TwoStateAt.NT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.F#Handle(TwoStateAt.NT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1) } 
  Apply2(TwoStateAt.NT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.F#Handle(TwoStateAt.NT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1)
     == $Box(TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $heap, $self, $fh$0x#0, $Unbox($fh$0x#1): ref)));

axiom (forall TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: int, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box :: 
  { Requires2(TwoStateAt.NT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.F#Handle(TwoStateAt.NT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1) } 
  Requires2(TwoStateAt.NT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.F#Handle(TwoStateAt.NT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1)
     == TwoStateAt.NT.F#requires(TwoStateAt.NT.F$Y, $prevHeap, $heap, $self, $fh$0x#0, $Unbox($fh$0x#1): ref));

axiom (forall $bx: Box, 
    TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: int, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box :: 
  { Reads2(TwoStateAt.NT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.F#Handle(TwoStateAt.NT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1)[$bx] } 
  Reads2(TwoStateAt.NT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.F#Handle(TwoStateAt.NT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1)[$bx]
     == 
    ($Unbox($bx): ref
     == $Unbox($fh$0x#1): ref));

axiom (forall TwoStateAt.NT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: int, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: ref :: 
  { TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $heap, $self, $fh$0x#0, $fh$0x#1) } 
  TwoStateAt.NT.F(TwoStateAt.NT.F$Y, $prevHeap, $heap, $self, $fh$0x#0, $fh$0x#1)
     == $Unbox(Apply2(TwoStateAt.NT.F$Y, 
        Tclass.TwoStateAt.Cell(), 
        TInt, 
        $heap, 
        TwoStateAt.NT.F#Handle(TwoStateAt.NT.F$Y, $prevHeap, $self), 
        $fh$0x#0, 
        $Box($fh$0x#1))): int);

function TwoStateAt.OT.F#Handle(Ty, Ty, Heap, Box) : HandleType;

axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: Box, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Apply3(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.F#Handle(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  Apply3(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.F#Handle(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == $Box(TwoStateAt.OT.F(TwoStateAt.OT$X, 
        TwoStateAt.OT.F$Y, 
        $prevHeap, 
        $heap, 
        $self, 
        $fh$0x#0, 
        $fh$0x#1, 
        $Unbox($fh$0x#2): ref)));

axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: Box, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Requires3(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.F#Handle(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  Requires3(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.F#Handle(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == TwoStateAt.OT.F#requires(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      $prevHeap, 
      $heap, 
      $self, 
      $fh$0x#0, 
      $fh$0x#1, 
      $Unbox($fh$0x#2): ref));

axiom (forall $bx: Box, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: Box, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Reads3(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.F#Handle(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)[$bx] } 
  Reads3(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.F#Handle(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $self), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)[$bx]
     == 
    ($Unbox($bx): ref
     == $Unbox($fh$0x#2): ref));

axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.F$Y: Ty, 
    $prevHeap: Heap, 
    $self: Box, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: ref :: 
  { TwoStateAt.OT.F(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      $prevHeap, 
      $heap, 
      $self, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  TwoStateAt.OT.F(TwoStateAt.OT$X, 
      TwoStateAt.OT.F$Y, 
      $prevHeap, 
      $heap, 
      $self, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == $Unbox(Apply3(TwoStateAt.OT$X, 
        TwoStateAt.OT.F$Y, 
        Tclass.TwoStateAt.Cell(), 
        TInt, 
        $heap, 
        TwoStateAt.OT.F#Handle(TwoStateAt.OT$X, TwoStateAt.OT.F$Y, $prevHeap, $self), 
        $fh$0x#0, 
        $fh$0x#1, 
        $Box($fh$0x#2))): int);

function TwoStateAt.DT.G#Handle(Ty, Ty, Heap) : HandleType;

axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Apply3(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.G#Handle(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  Apply3(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.G#Handle(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == $Box(TwoStateAt.DT.G(TwoStateAt.DT$X, 
        TwoStateAt.DT.G$Y, 
        $prevHeap, 
        $heap, 
        $fh$0x#0, 
        $fh$0x#1, 
        $Unbox($fh$0x#2): ref)));

axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Requires3(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.G#Handle(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  Requires3(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.G#Handle(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == TwoStateAt.DT.G#requires(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      $prevHeap, 
      $heap, 
      $fh$0x#0, 
      $fh$0x#1, 
      $Unbox($fh$0x#2): ref));

axiom (forall $bx: Box, 
    TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box :: 
  { Reads3(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.G#Handle(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)[$bx] } 
  Reads3(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.DT.G#Handle(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)[$bx]
     == 
    ($Unbox($bx): ref
     == $Unbox($fh$0x#2): ref));

axiom (forall TwoStateAt.DT$X: Ty, 
    TwoStateAt.DT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: ref :: 
  { TwoStateAt.DT.G(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      $prevHeap, 
      $heap, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2) } 
  TwoStateAt.DT.G(TwoStateAt.DT$X, 
      TwoStateAt.DT.G$Y, 
      $prevHeap, 
      $heap, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2)
     == $Unbox(Apply3(TwoStateAt.DT$X, 
        TwoStateAt.DT.G$Y, 
        Tclass.TwoStateAt.Cell(), 
        TInt, 
        $heap, 
        TwoStateAt.DT.G#Handle(TwoStateAt.DT$X, TwoStateAt.DT.G$Y, $prevHeap), 
        $fh$0x#0, 
        $fh$0x#1, 
        $Box($fh$0x#2))): int);

function TwoStateAt.NT.G#Handle(Ty, Heap) : HandleType;

axiom (forall TwoStateAt.NT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box :: 
  { Apply2(TwoStateAt.NT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.G#Handle(TwoStateAt.NT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1) } 
  Apply2(TwoStateAt.NT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.G#Handle(TwoStateAt.NT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1)
     == $Box(TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $heap, $fh$0x#0, $Unbox($fh$0x#1): ref)));

axiom (forall TwoStateAt.NT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box :: 
  { Requires2(TwoStateAt.NT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.G#Handle(TwoStateAt.NT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1) } 
  Requires2(TwoStateAt.NT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.G#Handle(TwoStateAt.NT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1)
     == TwoStateAt.NT.G#requires(TwoStateAt.NT.G$Y, $prevHeap, $heap, $fh$0x#0, $Unbox($fh$0x#1): ref));

axiom (forall $bx: Box, 
    TwoStateAt.NT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box :: 
  { Reads2(TwoStateAt.NT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.G#Handle(TwoStateAt.NT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1)[$bx] } 
  Reads2(TwoStateAt.NT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.NT.G#Handle(TwoStateAt.NT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1)[$bx]
     == 
    ($Unbox($bx): ref
     == $Unbox($fh$0x#1): ref));

axiom (forall TwoStateAt.NT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: ref :: 
  { TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $heap, $fh$0x#0, $fh$0x#1) } 
  TwoStateAt.NT.G(TwoStateAt.NT.G$Y, $prevHeap, $heap, $fh$0x#0, $fh$0x#1)
     == $Unbox(Apply2(TwoStateAt.NT.G$Y, 
        Tclass.TwoStateAt.Cell(), 
        TInt, 
        $heap, 
        TwoStateAt.NT.G#Handle(TwoStateAt.NT.G$Y, $prevHeap), 
        $fh$0x#0, 
        $Box($fh$0x#1))): int);

function TwoStateAt.OT.G#Handle(Ty, Ty, Heap) : HandleType;

axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box, 
    $fh$0x#3: Box :: 
  { Apply4(#$OT(TwoStateAt.OT$X), 
      TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.G#Handle(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3) } 
  Apply4(#$OT(TwoStateAt.OT$X), 
      TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.G#Handle(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3)
     == $Box(TwoStateAt.OT.G(TwoStateAt.OT$X, 
        TwoStateAt.OT.G$Y, 
        $prevHeap, 
        $heap, 
        $fh$0x#0, 
        $fh$0x#1, 
        $fh$0x#2, 
        $Unbox($fh$0x#3): ref)));

axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box, 
    $fh$0x#3: Box :: 
  { Requires4(#$OT(TwoStateAt.OT$X), 
      TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.G#Handle(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3) } 
  Requires4(#$OT(TwoStateAt.OT$X), 
      TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.G#Handle(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3)
     == TwoStateAt.OT.G#requires(TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      $prevHeap, 
      $heap, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $Unbox($fh$0x#3): ref));

axiom (forall $bx: Box, 
    TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box, 
    $fh$0x#3: Box :: 
  { Reads4(#$OT(TwoStateAt.OT$X), 
      TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.G#Handle(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3)[$bx] } 
  Reads4(#$OT(TwoStateAt.OT$X), 
      TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      Tclass.TwoStateAt.Cell(), 
      TInt, 
      $heap, 
      TwoStateAt.OT.G#Handle(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap), 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3)[$bx]
     == 
    ($Unbox($bx): ref
     == $Unbox($fh$0x#3): ref));

axiom (forall TwoStateAt.OT$X: Ty, 
    TwoStateAt.OT.G$Y: Ty, 
    $prevHeap: Heap, 
    $heap: Heap, 
    $fh$0x#0: Box, 
    $fh$0x#1: Box, 
    $fh$0x#2: Box, 
    $fh$0x#3: ref :: 
  { TwoStateAt.OT.G(TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      $prevHeap, 
      $heap, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3) } 
  TwoStateAt.OT.G(TwoStateAt.OT$X, 
      TwoStateAt.OT.G$Y, 
      $prevHeap, 
      $heap, 
      $fh$0x#0, 
      $fh$0x#1, 
      $fh$0x#2, 
      $fh$0x#3)
     == $Unbox(Apply4(#$OT(TwoStateAt.OT$X), 
        TwoStateAt.OT$X, 
        TwoStateAt.OT.G$Y, 
        Tclass.TwoStateAt.Cell(), 
        TInt, 
        $heap, 
        TwoStateAt.OT.G#Handle(TwoStateAt.OT$X, TwoStateAt.OT.G$Y, $prevHeap), 
        $fh$0x#0, 
        $fh$0x#1, 
        $fh$0x#2, 
        $Box($fh$0x#3))): int);

implementation Impl$$TwoStateAt.__default.TestOthers4(d0#0: DatatypeType, nt#0: int, ot#0: Box, r#0: ref, u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var d1#0: DatatypeType
     where $Is(d1#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
       && $IsAlloc(d1#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap);
  var $Heap_at_0: Heap;
  var f0#0_0: HandleType
     where $Is(f0#0_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(f0#0_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt), 
        $Heap);
  var f1#0_0: HandleType
     where $Is(f1#0_0, Tclass._System.___hFunc2(TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(f1#0_0, Tclass._System.___hFunc2(TInt, Tclass.TwoStateAt.Cell(), TInt), $Heap);
  var f2#0_0: HandleType
     where $Is(f2#0_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(f2#0_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt), 
        $Heap);
  var f3#0_0: HandleType
     where $Is(f3#0_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(f3#0_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt), 
        $Heap);
  var g0#1_0: HandleType
     where $Is(g0#1_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(g0#1_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt), 
        $Heap);
  var g1#1_0: HandleType
     where $Is(g1#1_0, Tclass._System.___hFunc2(TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(g1#1_0, Tclass._System.___hFunc2(TInt, Tclass.TwoStateAt.Cell(), TInt), $Heap);
  var g2#1_0: HandleType
     where $Is(g2#1_0, 
        Tclass._System.___hFunc4(#$OT(Tclass.TwoStateAt.Cell()), 
          Tclass.TwoStateAt.Cell(), 
          TInt, 
          Tclass.TwoStateAt.Cell(), 
          TInt))
       && $IsAlloc(g2#1_0, 
        Tclass._System.___hFunc4(#$OT(Tclass.TwoStateAt.Cell()), 
          Tclass.TwoStateAt.Cell(), 
          TInt, 
          Tclass.TwoStateAt.Cell(), 
          TInt), 
        $Heap);
  var h0#2_0: HandleType
     where $Is(h0#2_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(h0#2_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt), 
        $Heap);
  var h1#2_0: HandleType
     where $Is(h1#2_0, Tclass._System.___hFunc2(TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(h1#2_0, Tclass._System.___hFunc2(TInt, Tclass.TwoStateAt.Cell(), TInt), $Heap);
  var h2#2_0: HandleType
     where $Is(h2#2_0, 
        Tclass._System.___hFunc4(#$OT(Tclass.TwoStateAt.Cell()), 
          Tclass.TwoStateAt.Cell(), 
          TInt, 
          Tclass.TwoStateAt.Cell(), 
          TInt))
       && $IsAlloc(h2#2_0, 
        Tclass._System.___hFunc4(#$OT(Tclass.TwoStateAt.Cell()), 
          Tclass.TwoStateAt.Cell(), 
          TInt, 
          Tclass.TwoStateAt.Cell(), 
          TInt), 
        $Heap);
  var h3#2_0: HandleType
     where $Is(h3#2_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt))
       && $IsAlloc(h3#2_0, 
        Tclass._System.___hFunc3(Tclass.TwoStateAt.Cell(), TInt, Tclass.TwoStateAt.Cell(), TInt), 
        $Heap);

    // AddMethodImpl: TestOthers4, Impl$$TwoStateAt.__default.TestOthers4
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(626,73): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(627,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(627,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(333);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(627,26)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(627,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(628,12)
    assume true;
    assume true;
    d1#0 := #TwoStateAt.DT.Blue($Box(c#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(628,21)"} true;
    $Heap_at_0 := $Heap;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(631,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(632,20)
        assume true;
        assert 5 != $FunctionContextHeight;
        assert $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), old($Heap));
        assume true;
        f0#0_0 := TwoStateAt.DT.F#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap), d0#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(632,31)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(633,20)
        assume true;
        assert 10 != $FunctionContextHeight;
        assume true;
        f1#0_0 := TwoStateAt.NT.F#Handle(TInt, old($Heap), nt#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(633,31)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(634,20)
        assume true;
        assert 15 != $FunctionContextHeight;
        assert $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), old($Heap));
        assume true;
        f2#0_0 := TwoStateAt.OT.F#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap), ot#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(634,31)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(635,20)
        assume true;
        assert 5 != $FunctionContextHeight;
        assert $IsAlloc(d1#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), old($Heap));
        assume true;
        f3#0_0 := TwoStateAt.DT.F#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap), d1#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(635,31)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(636,12)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(637,20)
            assume true;
            assert 8 != $FunctionContextHeight;
            assume true;
            g0#1_0 := TwoStateAt.DT.G#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(637,37)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(638,20)
            assume true;
            assert 13 != $FunctionContextHeight;
            assume true;
            g1#1_0 := TwoStateAt.NT.G#Handle(TInt, old($Heap));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(638,31)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(639,20)
            assume true;
            assert 17 != $FunctionContextHeight;
            assume true;
            g2#1_0 := TwoStateAt.OT.G#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(639,37)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(640,12)
            if (*)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(641,20)
                assume true;
                assert 8 != $FunctionContextHeight;
                assume true;
                h0#2_0 := TwoStateAt.DT.G#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap));
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(641,31)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(642,20)
                assume true;
                assert 13 != $FunctionContextHeight;
                assume true;
                h1#2_0 := TwoStateAt.NT.G#Handle(TInt, old($Heap));
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(642,31)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(643,20)
                assume true;
                assert 17 != $FunctionContextHeight;
                assume true;
                h2#2_0 := TwoStateAt.OT.G#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap));
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(643,31)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(644,20)
                assume true;
                assert 8 != $FunctionContextHeight;
                assume true;
                h3#2_0 := TwoStateAt.DT.G#Handle(Tclass.TwoStateAt.Cell(), TInt, old($Heap));
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(644,31)"} true;
            }
            else
            {
            }
        }
    }

  after_0:
}



procedure CheckWellformed$$TwoStateAt.__default.FieldAccess(d0#0: DatatypeType
       where $Is(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
         && $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap)
         && $IsA#TwoStateAt.DT(d0#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()))
         && $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TwoStateAt.__default.FieldAccess(d0#0: DatatypeType
       where $Is(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
         && $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap)
         && $IsA#TwoStateAt.DT(d0#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()))
         && $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0));
  // user-defined preconditions
  requires TwoStateAt.DT.Blue_q(d0#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TwoStateAt.__default.FieldAccess(d0#0: DatatypeType
       where $Is(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
         && $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap)
         && $IsA#TwoStateAt.DT(d0#0), 
    nt#0: int where LitInt(0) <= nt#0 && nt#0 < 86, 
    ot#0: Box
       where $IsBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()))
         && $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.TwoStateAt.Cell())
         && $IsAlloc(r#0, Tclass.TwoStateAt.Cell(), $Heap), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._System.Tuple0())
         && $IsAlloc(u#0, Tclass._System.Tuple0(), $Heap)
         && $IsA#_System.Tuple0(u#0))
   returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  // user-defined preconditions
  requires TwoStateAt.DT.Blue_q(d0#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TwoStateAt.__default.FieldAccess(d0#0: DatatypeType, nt#0: int, ot#0: Box, r#0: ref, u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(c#0, Tclass.TwoStateAt.Cell(), $Heap);
  var $nw: ref;
  var x##0: int;
  var d1#0: DatatypeType
     where $Is(d1#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()))
       && $IsAlloc(d1#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap);
  var $Heap_at_0: Heap;
  var f0#0_0: ref
     where $Is(f0#0_0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(f0#0_0, Tclass.TwoStateAt.Cell(), $Heap);
  var f1#0_0: int;
  var f2#0_0: int;
  var f3#0_0: ref
     where $Is(f3#0_0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(f3#0_0, Tclass.TwoStateAt.Cell(), $Heap);
  var g0#1_0: int;
  var g1#1_0: int;
  var g2#1_0: int;
  var h0#2_0: int;
  var h1#2_0: int;
  var h2#2_0: int;
  var h3#2_0: int;
  var f0#3_0: ref
     where $Is(f0#3_0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(f0#3_0, Tclass.TwoStateAt.Cell(), $Heap);
  var f1#3_0: int;
  var f2#3_0: int;
  var f3#3_0: ref
     where $Is(f3#3_0, Tclass.TwoStateAt.Cell())
       && $IsAlloc(f3#3_0, Tclass.TwoStateAt.Cell(), $Heap);
  var g0#4_0: int;
  var g1#4_0: int;
  var g2#4_0: int;
  var h0#5_0: int;
  var h1#5_0: int;
  var h2#5_0: int;
  var h3#5_0: int;

    // AddMethodImpl: FieldAccess, Impl$$TwoStateAt.__default.FieldAccess
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_TwoStateAt._default.Opaque)
       == StartFuel_TwoStateAt._default.Opaque;
    assume AsFuelBottom(StartFuelAssert_TwoStateAt._default.Opaque)
       == StartFuelAssert_TwoStateAt._default.Opaque;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(650,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(651,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(651,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(333);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$TwoStateAt.Cell.__ctor(x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(651,26)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(651,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(652,12)
    assume true;
    assume true;
    d1#0 := #TwoStateAt.DT.Blue($Box(c#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(652,21)"} true;
    $Heap_at_0 := $Heap;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(655,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(656,20)
        assume true;
        assert TwoStateAt.DT.Blue_q(d0#0);
        assert $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), old($Heap));
        assume true;
        f0#0_0 := $Unbox(TwoStateAt.DT.value(d0#0)): ref;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(656,35)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(657,20)
        assume true;
        assume true;
        f1#0_0 := TwoStateAt.NT.value(nt#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(657,35)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(658,20)
        assume true;
        assert $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), old($Heap));
        assume true;
        f2#0_0 := TwoStateAt.OT.value(Tclass.TwoStateAt.Cell(), ot#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(658,35)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(659,20)
        assume true;
        assert TwoStateAt.DT.Blue_q(d1#0);
        assert $IsAlloc(d1#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), old($Heap));
        assume true;
        f3#0_0 := $Unbox(TwoStateAt.DT.value(d1#0)): ref;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(659,35)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(660,12)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(661,20)
            assume true;
            assume true;
            g0#1_0 := TwoStateAt.DT.sc(Tclass.TwoStateAt.Cell());
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(661,38)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(662,20)
            assume true;
            assume true;
            g1#1_0 := TwoStateAt.NT.sc();
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(662,32)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(663,20)
            assume true;
            assume true;
            g2#1_0 := TwoStateAt.OT.sc(Tclass.TwoStateAt.Cell());
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(663,38)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(664,12)
            if (*)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(665,20)
                assume true;
                assume true;
                h0#2_0 := TwoStateAt.DT.sc(Tclass.TwoStateAt.Cell());
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(665,32)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(666,20)
                assume true;
                assume true;
                h1#2_0 := TwoStateAt.NT.sc();
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(666,32)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(667,20)
                assume true;
                assume true;
                h2#2_0 := TwoStateAt.OT.sc(Tclass.TwoStateAt.Cell());
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(667,32)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(668,20)
                assume true;
                assume true;
                h3#2_0 := TwoStateAt.DT.sc(Tclass.TwoStateAt.Cell());
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(668,32)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(669,12)
                if (*)
                {
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(670,20)
                    assume true;
                    assert TwoStateAt.DT.Blue_q(d0#0);
                    assert $IsAlloc(d0#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap_at_0);
                    assume true;
                    f0#3_0 := $Unbox(TwoStateAt.DT.value(d0#0)): ref;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(670,41)"} true;
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(671,20)
                    assume true;
                    assume true;
                    f1#3_0 := TwoStateAt.NT.value(nt#0);
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(671,41)"} true;
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(672,20)
                    assume true;
                    assert $IsAllocBox(ot#0, #$OT(Tclass.TwoStateAt.Cell()), $Heap_at_0);
                    assume true;
                    f2#3_0 := TwoStateAt.OT.value(Tclass.TwoStateAt.Cell(), ot#0);
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(672,41)"} true;
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(673,20)
                    assume true;
                    assert TwoStateAt.DT.Blue_q(d1#0);
                    assert $IsAlloc(d1#0, Tclass.TwoStateAt.DT(Tclass.TwoStateAt.Cell()), $Heap_at_0);
                    assume true;
                    f3#3_0 := $Unbox(TwoStateAt.DT.value(d1#0)): ref;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(673,41)"} true;
                }
                else
                {
                    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(674,12)
                    if (*)
                    {
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(675,20)
                        assume true;
                        assume true;
                        g0#4_0 := TwoStateAt.DT.sc(Tclass.TwoStateAt.Cell());
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(675,44)"} true;
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(676,20)
                        assume true;
                        assume true;
                        g1#4_0 := TwoStateAt.NT.sc();
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(676,38)"} true;
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(677,20)
                        assume true;
                        assume true;
                        g2#4_0 := TwoStateAt.OT.sc(Tclass.TwoStateAt.Cell());
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(677,44)"} true;
                    }
                    else
                    {
                        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(678,12)
                        if (*)
                        {
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(679,20)
                            assume true;
                            assume true;
                            h0#5_0 := TwoStateAt.DT.sc(Tclass.TwoStateAt.Cell());
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(679,38)"} true;
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(680,20)
                            assume true;
                            assume true;
                            h1#5_0 := TwoStateAt.NT.sc();
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(680,38)"} true;
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(681,20)
                            assume true;
                            assume true;
                            h2#5_0 := TwoStateAt.OT.sc(Tclass.TwoStateAt.Cell());
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(681,38)"} true;
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(682,20)
                            assume true;
                            assume true;
                            h3#5_0 := TwoStateAt.DT.sc(Tclass.TwoStateAt.Cell());
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Twostate-Verification.dfy(682,38)"} true;
                        }
                        else
                        {
                        }
                    }
                }
            }
        }
    }

  after_0:
}



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$TwoStateAt.__default.reveal__Opaque(previous$Heap: Heap, current$Heap: Heap);
  free requires 24 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



const MoreFuel_TwoStateAt._default.Opaque4: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$TwoStateAt.__default.reveal__Opaque(previous$Heap: Heap, current$Heap: Heap);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel_TwoStateAt._default.Opaque
     == $LS(MoreFuel_TwoStateAt._default.Opaque4);
  free ensures StartFuelAssert_TwoStateAt._default.Opaque
     == $LS($LS(MoreFuel_TwoStateAt._default.Opaque4));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel_TwoStateAt._default.Opaque4)
     == MoreFuel_TwoStateAt._default.Opaque4;



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

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Cell: TyTagFamily;

const unique tytagFamily$DT: TyTagFamily;

const unique tytagFamily$NT: TyTagFamily;

const unique tytagFamily$OT: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$data: NameFamily;
