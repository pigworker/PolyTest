module Glom where

import Data.Char

prefix :: String -> String -> Bool
prefix [] _ = True
prefix (c : p) (d : s) | c == d = prefix p s
prefix _ _ = False

munch :: [String] -> [String]
munch [] = []
munch (l : ls)
  | prefix "\\end{code}" l = crunch ls
  | otherwise =
      (if all isSpace l then id else (l :)) (munch ls)

crunch :: [String] -> [String]
crunch [] = []
crunch (l : ls)
  | prefix "\\begin{code}" l = munch ls
  | otherwise = crunch ls


glom :: String -> String -> IO ()
glom r w = readFile r >>=
  (writeFile w . unlines . crunch . lines)
