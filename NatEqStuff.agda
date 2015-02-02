module NatEqStuff where

open import Eq
open import CMon

data Dec (P : Set) : Set where
  yes : P -> Dec P
  no  : (np : P -> Zero) -> Dec P

NoConf : Nat -> Nat -> Set
NoConf  ze      ze      =  One
NoConf  ze      (su y)  =  Zero
NoConf  (su x)  ze      =  Zero
NoConf  (su x)  (su y)  =  x == y

noConf : {x y : Nat} -> x == y -> NoConf x y
noConf {ze}   refl = <>
noConf {su x} refl = refl

decEq : (x y : Nat) -> Dec (x == y)
decEq  ze      ze                        = yes refl
decEq  ze      (su y)                    = no noConf
decEq  (su x)  ze                        = no noConf
decEq  (su x)  (su y)   with  decEq x y
decEq  (su x)  (su .x)  |     yes refl   = yes refl
decEq  (su x)  (su y)   |     no nq      = no \ q -> nq (noConf q)
