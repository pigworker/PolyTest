module CMon where

open import Eq

data Nat : Set where
  ze : Nat
  su : (n : Nat) -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO ze #-}
{-# BUILTIN SUC su #-}

_+_ : Nat -> Nat -> Nat
ze    +  n  =  n
su m  +  n  =  su (m + n)
infixr 4 _+_

data Zero : Set where
record One : Set where constructor <>

_>_ : Nat -> Nat -> Set
ze    >  _     =  Zero
su m  >  ze    =  One
su m  >  su n  =  m > n

data Fin (n : Nat) : Set where [_<_] : (m : Nat)(_ : n > m) -> Fin n

fin : {n : Nat}(m : Nat){_ : n > m} -> Fin n
fin m {p} = [ m < p ]

data Vec (X : Set) : Nat -> Set where
  <> : Vec X ze
  _,_ : {n : Nat} -> X -> Vec X n -> Vec X (su n)
infixr 3 _,_

vec : {n : Nat} -> {X : Set} -> X -> Vec X n
vec {ze}    x  = <>
vec {su n}  x  = x , vec x

_$$_ : {n : Nat}{S T : Set} -> Vec (S -> T) n -> Vec S n -> Vec T n
_$$_ {ze}    <>        <>        = <>
_$$_ {su n}  (f , fs)  (s , ss)  = f s , fs $$ ss

infixl 9 _$$_

proj : {n : Nat}{X : Set} -> Vec X n -> Fin n -> X
proj {ze}    _         [ _ < () ]
proj {su n}  (x , xs)  [ ze < _ ]    = x
proj {su n}  (x , xs)  [ su i < p ]  = proj xs [ i < p ]

data CMX (n : Nat) : Set where
  var : Fin n -> CMX n
  _><_ : (s t : CMX n) -> CMX n
  neu : CMX n

infixr 4 _><_

vi : {n : Nat}(m : Nat){_ : n > m} -> CMX n
vi m {p} = var [ m < p ]

delta : {n : Nat} -> Fin n -> Vec Nat n
delta {ze}   [ _ < () ]
delta {su n} [ ze < _ ]    = (1 , vec 0)
delta {su n} [ su i < p ]  = (0 , delta [ i < p ])

count : {n : Nat} -> CMX n -> Vec Nat n
count (var x)   = delta x
count (s >< t)  = vec _+_ $$ count s $$ count t
count neu       = vec 0


Assoc : {X : Set}(f : X -> X -> X) -> Set
Assoc f = forall x y z -> f (f x y) z == f x (f y z)

record CMon (X : Set) : Set where
  field
    ne  : X
    op  : X -> X -> X
    absorb     : (x : X) ->       x == op ne x
    commute    : (x y : X) ->     op x y == op y x
    assocM     : Assoc op
open CMon public

brosba : {X : Set}(C : CMon X)(x : X) -> x == op C x (ne C)
brosba C x = absorb C x =o= commute C (ne C) x

mid4 : {X : Set}(C : CMon X)(w x y z : X) ->
  op C (op C w x) (op C y z) == op C (op C w y) (op C x z)
mid4 C w x y z =  assocM C w x (op C y z) =o=
                  (op C w $= (  sym (assocM C x y z) =o=
                                op C $= commute C x y =$= refl =o=
                                assocM C y x z)) =o=
                  sym (assocM C w y (op C x z))

eval : forall {n X}(C : CMon X)(g : Vec X n) -> CMX n -> X
eval C g (var y)   = proj g y
eval C g (s >< t)  = op C (eval C g s) (eval C g t)
eval C g neu       = ne C

mult : forall {X}(C : CMon X) -> Nat -> X -> X
mult C ze x      = ne C
mult C (su n) x  = op C (mult C n x) x

norm : forall {n : Nat}{X : Set}(C : CMon X)(g : Vec X n) -> Vec Nat n -> X
norm C <>       <>        = ne C
norm C (x , xs) (m , ms)  = op C (mult C m x) (norm C xs ms)

zeLem : {n : Nat}{X : Set}(C : CMon X)(g : Vec X n) -> ne C == norm C g (vec 0)
zeLem C <>        = refl
zeLem C (x , xs)  = zeLem C xs =o= absorb C (norm C xs (vec 0))

distLem : {X : Set}(C : CMon X)(l m : Nat)(x : X) ->
  op C (mult C l x) (mult C m x) == mult C (l + m) x
distLem C ze      m x  = sym (absorb C (mult C m x))
distLem C (su l)  m x  =  assocM C (mult C l x) x (mult C m x) =o=
                          (op C (mult C l x) $= commute C x (mult C m x)) =o=
                          sym (assocM C (mult C l x) (mult C m x) x) =o=
                          op C $= distLem C l m x =$= refl

+Lem : forall {n X}(C : CMon X)(g : Vec X n) ->
  (ls ms : Vec Nat n) ->
  op C (norm C g ls) (norm C g ms) == norm C g (vec _+_ $$ ls $$ ms)
+Lem C <>       <>       <>        = sym (absorb C (ne C))
+Lem C (x , xs) (l , ls) (m , ms)  =
  mid4 C (mult C l x) (norm C xs ls) (mult C m x) (norm C xs ms) =o=
  (op C $= distLem C l m x =$= +Lem C xs ls ms)

varLem : forall {n X}(C : CMon X)(g : Vec X n) i ->
  proj g i == norm C g (delta i)
varLem C <>       [ _ < () ]
varLem C (x , xs) [ ze < _ ] =
  brosba C x =o= (op C $= absorb C x =$= zeLem C xs)
varLem C (x , xs) [ su i < p ] =
  varLem C xs [ i < p ] =o= absorb C (norm C xs (delta [ i < p ]))

normThm : forall {n X}(C : CMon X)(g : Vec X n)(s : CMX n) ->
            eval C g s == norm C g (count s)
normThm C g (var x)   =  varLem C g x
normThm C g (s >< t)  =  (op C $= normThm C g s =$= normThm C g t ) =o=
                         +Lem C g (count s) (count t)
normThm C g neu = zeLem C g

cmonThm : forall {n X}(C : CMon X)(g : Vec X n)(s t : CMX n) ->
            count s == count t -> eval C g s == eval C g t
cmonThm C g s t q = normThm C g s =o= norm C g $= q =o= sym (normThm C g t)

+ze : {n : Nat} -> n == n + ze
+ze {ze}    = refl
+ze {su n}  = su $= +ze

+su : (m n : Nat) -> su (m + n) == m + su n
+su ze      n  = refl
+su (su m)  n  = su $= +su m n

+comm : (m n : Nat) -> m + n == n + m
+comm ze      n  = +ze
+comm (su m)  n  = (su $= +comm m n) =o= +su n m

+assoc : (l m n : Nat) -> (l + m) + n == l + (m + n)
+assoc ze     m n  = refl
+assoc (su l) m n  = su $= +assoc l m n

NAT : CMon Nat
NAT = record {  ne = ze;  op = _+_;
                absorb = \ x -> refl; commute = +comm; assocM = +assoc }

_*_ : Nat -> Nat -> Nat
x * y = mult NAT x y
infixr 5 _*_

*dist+ : (a b c : Nat) -> a * (b + c) == a * b + a * c
*dist+ ze      b c  = refl
*dist+ (su a)  b c  rewrite *dist+ a b c =
  cmonThm NAT ((a * b) , (a * c) , b , c , <>)
   ((vi 0 >< vi 1) >< (vi 2 >< vi 3)) ((vi 0 >< vi 2) >< (vi 1 >< vi 3)) refl

+dist* : (a b c : Nat) -> (a + b) * c == a * c + b * c
+dist* a b c = sym (distLem NAT a b c)

multOut : (a b c d : Nat) ->
  (a + b) * (c + d) == (a * c + a * d) + (b * c + b * d)
multOut a b c d =
  +dist* a b (c + d) =o= (_+_ $= (*dist+ a c d) =$= (*dist+ b c d))

record Ring {X : Set}(C : CMon X) : Set where
  field
    mu : X -> X -> X
    assocR  : Assoc mu
    *DistZ  : (x : X) ->      mu x (ne C) == ne C
    *Dist+  : (x y z : X) ->  mu x (op C y z) == op C (mu x y) (mu x z)
    zDist*  : (x : X) ->      mu (ne C) x == ne C
    +Dist*  : (x y z : X) ->  mu (op C x y) z == op C (mu x z) (mu y z)
open Ring public

data RX (X : Set) : Set where
  rv     : X -> RX X
  rz     : RX X
  _r+_   : RX X -> RX X -> RX X
  _r*_   : RX X -> RX X -> RX X

rxEval : {X : Set}{C : CMon X}(R : Ring C) -> RX X -> X
rxEval R (rv x) = x
rxEval {C = C} R rz = ne C
rxEval {C = C} R (a r+ b) = op C (rxEval R a) (rxEval R b)
rxEval R (a r* b) = mu R (rxEval R a) (rxEval R b)

data NEL (X : Set) : Set
data List (X : Set) : Set

data NEL X where
  _,_ : X -> List X -> NEL X

data List X where
  <> : List X
  ! : NEL X -> List X


n1 : {X : Set} -> X -> NEL X
n1 x = x , <>

_+n+_ : {X : Set} -> NEL X -> NEL X -> NEL X
(x , <>)    +n+  ys  = x , ! ys
(x , ! xs)  +n+  ys  = x , ! (xs +n+ ys)

l1 : {X : Set} -> X -> List X
l1 x = ! (n1 x)

_+l+_ : {X : Set} -> List X -> List X -> List X
<>          +l+  ys  = ys
! (x , xs)  +l+  ys  = ! (x , xs +l+ ys)

appNil : {X : Set}(xs : List X) -> xs +l+ <> == xs
appNil <> = refl
appNil (! (x , xs)) = ! $= (_,_ x $= appNil xs)

_>>l=_ : {X Y : Set} -> List X -> (X -> List Y) -> List Y
<>          >>l= f  = <>
! (x , xs)  >>l= f  = f x +l+ (xs >>l= f)

_l$_ : {S T : Set} -> List (S -> T) -> List S -> List T
fs l$ ss = fs >>l= \ f -> ss >>l= \ s -> l1 (f s)

infixl 9 _l$_

rxNorm : {X : Set} -> RX X -> List (NEL X)
rxNorm (rv x)    = l1 (n1 x)
rxNorm rz        = <>
rxNorm (a r+ b)  = rxNorm a +l+ rxNorm b
rxNorm (a r* b)  = l1 _+n+_ l$ rxNorm a l$ rxNorm b

rxProd : {X : Set}{C : CMon X}(R : Ring C) -> NEL X -> X
rxProd R (x , <>)    = x
rxProd R (x , ! xs)  = mu R x (rxProd R xs)

rxSumProd : {X : Set}{C : CMon X}(R : Ring C) -> List (NEL X) -> X
rxSumProd {C = C} R <>              = ne C
rxSumProd {C = C} R (! (xs , xss))  = op C (rxProd R xs) (rxSumProd R xss)

rxSPLem : {X : Set}{C : CMon X}(R : Ring C)(xss yss : List (NEL X)) ->
  op C (rxSumProd R xss) (rxSumProd R yss) == rxSumProd R (xss +l+ yss)
rxSPLem {C = C} R <> yss
  = cmonThm C (rxSumProd R yss , <>) (neu >< vi 0) (vi 0) refl
rxSPLem {C = C} R (! (xs , xss)) yss =
  cmonThm C (rxProd R xs , rxSumProd R xss , rxSumProd R yss , <>)
     ((vi 0 >< vi 1) >< vi 2) (vi 0 >< (vi 1 >< vi 2)) refl =o=
  (op C (rxProd R xs)) $= rxSPLem R xss yss

rxMLem : {X : Set}{C : CMon X}(R : Ring C)(xs : NEL X)(ys : NEL X) ->
  mu R (rxProd R xs) (rxProd R ys) == rxProd R (xs +n+ ys)
rxMLem R (x , <>) ys = refl
rxMLem R (x , ! xs) ys =
  assocR R x (rxProd R xs) (rxProd R ys) =o=
  mu R x $= rxMLem R xs ys

rxDLem : {X : Set}{C : CMon X}(R : Ring C)(xs : NEL X)(yss : List (NEL X)) ->
  mu R (rxProd R xs) (rxSumProd R yss) ==
  rxSumProd R (l1 (_+n+_ xs) l$ yss)
rxDLem R xs <> = *DistZ R (rxProd R xs)
rxDLem {C = C} R xs (! (ys , yss)) =
  *Dist+ R (rxProd R xs) (rxProd R ys) (rxSumProd R yss) =o=
  op C $= rxMLem R xs ys =$= rxDLem R xs yss

rxPLem : {X : Set}{C : CMon X}(R : Ring C)(xss yss : List (NEL X)) ->
  mu R (rxSumProd R xss) (rxSumProd R yss) ==
  rxSumProd R (l1 _+n+_ l$ xss l$ yss)
rxPLem R <> yss = zDist* R (rxSumProd R yss)
rxPLem {C = C} R (! (xs , xss)) yss =
  +Dist* R (rxProd R xs) (rxSumProd R xss) (rxSumProd R yss) =o=
  (op C $= rxDLem R xs yss =$= rxPLem R xss yss) =o=
  rxSPLem R (l1 (_+n+_ xs) l$ yss) (l1 _+n+_ l$ xss l$ yss) =o=
  rxSumProd R $= (_+l+_ $= appNil (yss >>l= \ ys -> l1 (xs +n+ ys))
                        =$ (l1 _+n+_ l$ xss l$ yss)) 

rxThm : {X : Set}{C : CMon X}(R : Ring C)(e : RX X) ->
        rxEval R e == rxSumProd R (rxNorm e)
rxThm {C = C} R (rv x) = cmonThm C (x , <>) (vi 0) (vi 0 >< neu) refl
rxThm R rz = refl
rxThm {C = C} R (a r+ b) =
  (op C $= rxThm R a =$= rxThm R b) =o=
  rxSPLem R (rxNorm a) (rxNorm b)
rxThm R (a r* b) =
  (mu R $= rxThm R a =$= rxThm R b) =o=
  rxPLem R (rxNorm a) (rxNorm b)

*distZ : (a : Nat) -> a * 0 == 0
*distZ ze = refl
*distZ (su a) = _+_ $= *distZ a =$ 0


assoc* : Assoc _*_
assoc* ze b c = refl
assoc* (su a) b c = +dist* (a * b) b c =o= (_+_ $= assoc* a b c =$ (b * c))

NATR : Ring NAT
NATR = record {
         mu = _*_;
         assocR = assoc*;
         *DistZ = *distZ;
         *Dist+ = *dist+;
         zDist* = \ a -> refl;
         +Dist* = +dist*  }