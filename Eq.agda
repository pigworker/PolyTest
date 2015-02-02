module Eq where

postulate
      Level : Set
      lzero  : Level
      suc   : Level -> Level
      max   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  max   #-}

data _==_ {l : Level}{A : Set l}
          (a : A) : A -> Set l where
  refl : a == a
infix 0 _==_

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}


sym : {X : Set}{x y : X} -> x == y -> y == x
sym refl = refl

_=o=_ : {X : Set}{x y z : X} -> x == y -> y == z -> x == z
refl =o= q = q
infixr 2 _=o=_

_=$=_ : {S T : Set}{f g : S -> T}{x y : S} -> f == g -> x == y -> f x == g y
refl =$= refl = refl

_$=_ : {S T : Set}(f : S -> T){x y : S} -> x == y -> f x == f y
f $= q = refl =$= q

_=$_ : {S T : Set}{f g : S -> T} -> f == g -> (x : S) -> f x == g x
f =$ x = f =$= refl

infixl 9 _=$=_ _$=_ _=$_