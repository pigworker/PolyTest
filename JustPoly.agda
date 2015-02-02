module JustPoly where
data Nat : Set where
  ze  :         Nat
  su  : Nat ->  Nat
{-# BUILTIN NATURAL Nat #-}
_+_ : Nat -> Nat -> Nat
ze    + y  = y
su x  + y  = su (x + y)
infixr 5 _+_
_*_ : Nat -> Nat -> Nat
ze * x      = ze
su n * x  = n * x + x
infixr 6 _*_
sum : (f : Nat -> Nat) -> Nat -> Nat
sum f ze      = 0
sum f (su n)  = sum f n + f n
data _==_ {A : Set}(a : A) : A -> Set where refl : a == a
infix 0 _==_
_=!_!>_ : forall {X : Set}(x : X){y z} -> x == y -> y == z -> x == z
x =! refl !> q = q
_<!_!=_ : forall {X : Set}(x : X){y z} -> y == x -> y == z -> x == z
x <! refl != q = q
_!!! : forall {X : Set}(x : X) -> x == x
x !!! = refl
infixr 2 _!!! _=!_!>_ _<!_!=_
<^_^> : forall {X : Set}(x : X) -> x == x
<^ x ^> = refl
_=$=_ : {S T : Set}{f g : S -> T}{x y : S} -> f == g -> x == y -> f x == g y
refl =$= refl = refl
infixl 9 _=$=_
record One : Set where constructor <>
data Zero : Set where
_^_ : Nat -> Nat -> Nat
x ^ ze    = 1
x ^ su n  = (x ^ n) * x
data Add : Nat -> Nat -> Nat -> Set where
  zel   : forall {n} ->                   Add  ze      n       n
  zer   : forall {n} ->                   Add  n       ze      n
  susu  : forall {l m n} -> Add l m n ->  Add  (su l)  (su m)  (su (su n))
data Qoly : Nat -> Set where
  qk      : forall {n} ->                 Nat ->                    Qoly n
  qi      : forall {n} ->                                           Qoly (su n)
  qu      : forall {n} ->                 Qoly n ->                 Qoly n
  _q+_    : forall {n} ->      Qoly n ->  Qoly n ->                 Qoly n
  qtimes  : forall {l m n} ->  Qoly l ->  Qoly m ->  Add l m n ->   Qoly n
  qsum    : forall {n} -> Qoly n -> Qoly (su n)
infixr 5 _q+_
ql_qr : forall {n} -> Qoly n -> Nat -> Nat
ql qk n qr          x = n
ql qi qr            x = x
ql qu p qr          x = ql p qr (su x)
ql p q+ r qr        x = ql p qr x + ql r qr x
ql qtimes p r a qr  x = ql p qr x * ql r qr x
ql qsum p qr x = sum ql p qr x
sul : forall {l m n} -> Add l m n -> Add (su l) m (su n)
sul (zel {ze})    = zer
sul (zel {su n})  = susu zel
sul zer           = zer
sul (susu s)      = susu (sul s)
sur : forall {l m n} -> Add l m n -> Add l (su m) (su n)
sur zel           = zel 
sur (zer {ze})    = zel
sur (zer {su n})  = susu zer
sur (susu s)      = susu (sur s)
qd : forall {n} -> Qoly (su n) -> Qoly n
qd (qk _)                 = qk 0
qd qi                     = qk 1
qd (qu p)                 = qu (qd p)
qd (p q+ r)               = qd p q+ qd r
qd (qtimes p r zel)       = qtimes (qk (ql p qr 0)) (qd r)  zel
qd (qtimes p r zer)       = qtimes (qd p) (qk (ql r qr 0))  zer
qd (qtimes p r (susu a))  = qtimes (qd p) (qu r) (sur a) q+ qtimes p (qd r) (sul a)
qd (qsum p)               = p
add : (l m : Nat) -> Add l m (l + m)
add ze     m  = zel
add (su l) m  = sul (add l m)
_q*_ : forall {l m} -> Qoly l -> Qoly m -> Qoly (l + m)
_q*_ {l}{m} p r = qtimes p r (add l m)
infixr 6 _q*_
x1 : Qoly 1
x1 = qi
k0 : Nat -> Qoly 0
k0 n = qk n
_^^_ : forall {m} -> Qoly m -> (n : Nat) -> Qoly (n * m)
p ^^ ze = qk 1
p ^^ su n = (p ^^ n) q* p
record _&_ (S T : Set) : Set where constructor _/_; field fst : S ; snd : T
open _&_ public
TestEq : (k : Nat){n : Nat}(p r : Qoly n) -> Set
TestEq ze      p r =  One
TestEq (su k)  p r =  (ql p qr ze == ql r qr ze) & TestEq k (qu p) (qu r)
testLem : (n : Nat)(p r : Qoly n) -> TestEq (su n) p r -> (x : Nat) -> ql p qr x == ql r qr x
qkLem : (p : Qoly 0)(x y : Nat) -> ql p qr x == ql p qr y
qkLem (qk n)            x y  = refl
qkLem (qu p)            x y  =
  ql qu p qr x               =! refl !>
  ql p qr (su x)             =! qkLem p (su x) (su y) !>
  ql p qr (su y)             <! refl !=
  ql qu p qr y               !!!
qkLem (p q+ r)          x y  =
  ql (p q+ r) qr x           =! refl !>
  ql p qr x + ql r qr x      =! <^ _+_ ^> =$= qkLem p x y =$= qkLem r x y !>
  ql p qr y + ql r qr y      <! refl !=
  ql (p q+ r) qr y           !!!
qkLem (qtimes p r zel)  x y  =
  ql (p q* r) qr x           =! refl !>
  ql p qr x * ql r qr x      =! <^ _*_ ^> =$= qkLem p x y =$= qkLem r x y !>
  ql p qr y * ql r qr y      <! refl !=
  ql (p q* r) qr y           !!!
qkLem (qtimes p r zer)  x y  =
  ql (p q* r) qr x           =! refl !>
  ql p qr x * ql r qr x      =! <^ _*_ ^> =$= qkLem p x y =$= qkLem r x y !>
  ql p qr y * ql r qr y      <! refl !=
  ql (p q* r) qr y           !!!
qdLem : forall {n}(p : Qoly (su n)) x -> ql p qr (su x) == ql p qr x + ql qd p qr x
testQdLem : (k : Nat){n : Nat}(p r : Qoly (su n)) ->
  TestEq (su k) p r -> TestEq k (qd p) (qd r)
testLem ze      p r (q / <>) x         =
  ql p qr x                            =! qkLem p x ze !>
  ql p qr 0                            =! q !>
  ql r qr 0                            <! qkLem r x ze !=
  ql r qr x                            !!!
testLem (su n)  p r (q0 / qs)  ze      =
  ql p qr ze                           =! q0 !>
  ql r qr ze                           !!!
testLem (su n)  p r qs         (su x)  =
  ql p qr (su x)                       =! qdLem p x !>
  ql p qr x + ql qd p qr x
    =! (<^ _+_ ^>  =$=  testLem (su n) p r qs x =$= testLem n (qd p) (qd r) (testQdLem (su n) p r qs) x) !>
  ql r qr x + ql qd r qr x             <! qdLem r x !=
  ql r qr (su x)                       !!!
+cancel : forall w y {x z} -> w == y -> w + x == y + z -> x == z
testQdLem ze      p r  q          = <>
testQdLem (su k)  p r  (q0 / qs)  =
  +cancel (ql p qr 0) (ql r qr 0) q0 (
    ql p qr 0 + ql qd p qr 0  <! qdLem p 0 !=
    ql p qr 1                 =! fst qs !>
    ql r qr 1                 =! qdLem r 0 !>
    ql r qr 0 + ql qd r qr 0  !!! ) /
  testQdLem k (qu p) (qu r) qs
NoConf : Nat -> Nat -> Set
NoConf  ze      ze      =  One
NoConf  (su x)  (su y)  =  x == y
NoConf  _       _       =  Zero
noConf : forall {x y} -> x == y -> NoConf x y
noConf {ze}    refl = <>
noConf {su x}  refl = refl
+cancel ze      .ze      refl refl  = refl
+cancel (su w)  .(su w)  refl q     = +cancel w w refl (noConf q)
data Dec (P : Set) : Set where
  yes  : P ->            Dec P
  no   : (P -> Zero) ->  Dec P
decEq : (x y : Nat) -> Dec (x == y)
decEq  ze      ze                        = yes refl
decEq  ze      (su y)                    = no noConf
decEq  (su x)  ze                        = no noConf
decEq  (su x)  (su y)   with  decEq x y
decEq  (su x)  (su .x)  |     yes refl   = yes refl
decEq  (su x)  (su y)   |     no nq      = no \ q -> nq (noConf q)
testEq : (k : Nat){n : Nat}(p r : Qoly n) -> Dec (TestEq k p r)
testEq ze      p r = yes <>
testEq (su k)  p r with decEq (ql p qr 0) (ql r qr 0) | testEq k (qu p) (qu r)
... | yes y  | yes z  = yes (y / z)
... | yes y  | no np  = no \ xy -> np (snd xy)
... | no np  | _      = no \ xy -> np (fst xy)
TestStmt : (n : Nat)(p q : Qoly n) -> Set
TestStmt n p r with testEq (su n) p r
... | yes qs  = (x : Nat) -> ql p qr x == ql r qr x
... | no _   = One
testStmt : {n : Nat}(p r : Qoly n) -> TestStmt n p r
testStmt {n} p r with testEq (su n) p r
... | yes qs  = testLem n p r qs
... | no _    = <>
+assoc : (l m n : Nat) -> (l + m) + n == l + (m + n)
+assoc ze      m n  = refl
+assoc (su l)  m n  = <^ su ^> =$= +assoc l m n
+ze : {n : Nat} -> n == n + ze
+ze {ze}         =  refl
+ze {su n}       =  <^ su ^> =$= +ze
+su : (m n : Nat) -> su (m + n) == m + su n
+su ze      n    =  refl
+su (su m)  n    =  <^ su ^> =$= +su m n
+comm : (m n : Nat) -> m + n == n + m
+comm ze      n  =  +ze
+comm (su m)  n  =  su (m + n)  =! <^ su ^> =$= +comm m n !>
                    su (n + m)  =! +su n m !>
                    n + su m    !!!
mid4 : (w x y z : Nat) -> (w + x) + (y + z) == (w + y) + (x + z)
mid4 w x y z =
  (w + x) + (y + z)   =! +assoc w x (y + z) !>
  w + (x + (y + z))   =! <^ _+_ w ^> =$= (  x + (y + z)  <! +assoc x y z !=
                                            (x + y) + z  =! <^ _+_ ^> =$= +comm x y =$= <^ z ^> !>
                                            (y + x) + z  =! +assoc y x z !>
                                            y + (x + z)  !!!) !>
  w + (y + (x + z))   <! +assoc w y (x + z) !=
  (w + y) + (x + z)   !!!
*dist+ : (a b c : Nat) -> a * (b + c) == a * b + a * c
*dist+ ze      b c  = refl
*dist+ (su a)  b c  =
  a * (b + c) + (b + c)       =! <^ _+_ ^> =$= *dist+ a b c =$= <^ (b + c) ^> !>
  (a * b + a * c) + b + c     =! mid4 (a * b) (a * c) b c !>
  (a * b + b) + (a * c + c)   !!!
+dist* : (a b c : Nat) -> (a + b) * c == a * c + b * c
+dist* ze b c = refl
+dist* (su a) b c =
  (a + b) * c + c             =! <^ _+_ ^> =$= +dist* a b c =$= +ze !>
  (a * c + b * c) + (c + ze)  =! mid4 (a * c) (b * c) c ze !>
  (a * c + c) + (b * c + ze)  <! <^ _+_ (su a * c) ^> =$= +ze !=
  su a * c + b * c      !!!
qdLem (qk n)    x = n =! +ze !> n + 0 !!!
qdLem qi        x = 1 + x =! +comm 1 x !> x + 1 !!!
qdLem (qu p)    x = qdLem p (su x)
qdLem (p q+ r)  x =
  ql p qr (su x) + ql r qr (su x)                          =! <^ _+_ ^> =$= qdLem p x =$= qdLem r x !>
  (ql p qr x + ql qd p qr x) + (ql r qr x + ql qd r qr x)  =! mid4 (ql p qr x) (ql qd p qr x) (ql r qr x) (ql qd r qr x) !>
  ql p q+ r qr x + ql qd (p q+ r) qr x                     !!!
qdLem (qtimes p r zel) x =
  ql p qr (su x) * ql r qr (su x)                       =! <^ _*_ ^> =$= qkLem p (su x) 0 =$= qdLem r x !>
  ql p qr 0 * (ql r qr x + ql qd r qr x)                =! *dist+ (ql p qr 0) (ql r qr x) (ql qd r qr x) !>
  ql p qr 0 * ql r qr x + ql p qr 0 * ql qd r qr x      <! <^ _+_ ^> =$= (<^ _*_ ^> =$= qkLem p x 0 =$= refl) =$= refl !=
  ql p qr x * ql r qr x + ql p qr 0 * ql qd r qr x      !!!
qdLem (qtimes p r zer) x =
  ql p qr (su x) * ql r qr (su x)                       =! <^ _*_ ^> =$= qdLem p x =$= qkLem r (su x) 0 !>
  (ql p qr x + ql qd p qr x) * ql r qr 0                =! +dist* (ql p qr x) (ql qd p qr x) (ql r qr ze) !>
  ql p qr x * ql r qr 0 + ql qd p qr x * ql r qr 0      <! <^ _+_ ^> =$= (<^ _*_ (ql p qr x) ^> =$= qkLem r x 0) =$= refl !=
  ql p qr x * ql r qr x + ql qd p qr x * ql r qr 0      !!!
qdLem (qtimes p r (susu a)) x =
  ql p qr (su x) * ql r qr (su x)              =! <^ _*_ ^> =$= qdLem p x =$= refl !>
  (ql p qr x + ql qd p qr x) * ql r qr (su x)  =! +dist* (ql p qr x) (ql qd p qr x) (ql r qr (su x)) !>
  ql p qr x * ql r qr (su x) + ql qd p qr x * ql r qr (su x)
    =! <^ _+_ ^> =$= (<^ _*_ (ql p qr x) ^> =$= qdLem r x) =$= refl !>
  ql p qr x * (ql r qr x + ql qd r qr x) + ql qd p qr x * ql r qr (su x)
     =! <^ _+_ ^> =$= *dist+ (ql p qr x) (ql r qr x) (ql qd r qr x) =$= refl !>
  (ql p qr x * ql r qr x + ql p qr x * ql qd r qr x) + ql qd p qr x * ql r qr (su x)
     =! +assoc (ql p qr x * ql r qr x) _ _ !>
  ql p qr x * ql r qr x + ql p qr x * ql qd r qr x + ql qd p qr x * ql r qr (su x)
     =! <^ _+_ (ql p qr x * ql r qr x) ^> =$= +comm (ql p qr x * ql qd r qr x) (ql qd p qr x * ql r qr (su x)) !>
  ql p qr x * ql r qr x + ql qd p qr x * ql r qr (su x) + ql p qr x * ql qd r qr x !!!
qdLem (qsum p) x = refl
triangle  :  (x : Nat) -> 2 * sum (\ i -> i) (su x) == x * (x + 1)
triangle  =  testStmt (k0 2 q* qu (qsum x1)) (x1 q* (x1 q+ qk 1))
square    :  (x : Nat) -> sum (\ i -> 2 * i + 1) x == x ^ 2
square    =  testStmt (qsum (k0 2 q* x1 q+ qk 1)) (x1 ^^ 2)
cubes     :  (x : Nat) -> sum (\ i -> i ^ 3) x == (sum (\ i -> i) x) ^ 2
cubes     =  testStmt (qsum (x1 ^^ 3)) (qsum x1 ^^ 2)
