
module Tile where

data Tile = Empty
          | Wall
          | Pill
          | PowPill
          | Fruit
          | LambdaMan
          | Ghost 
          | OutBounds
          deriving (Eq)

instance Show Tile where
    show Empty     = " "
    show Wall      = "#"
    show Pill      = "."
    show PowPill   = "o"
    show Fruit     = "%"
    show LambdaMan = "\\"
    show Ghost     = "="
    show OutBounds = "X"

instance Read Tile where
    readsPrec _ value = 
        tryParse [(" ", Empty),
                  ("#", Wall),
                  (".", Pill),
                  ("o", PowPill),
                  ("%", Fruit),
                  ("\\", LambdaMan),
                  ("=", Ghost),
                  ("X", OutBounds)]
        where tryParse [] = []
              tryParse ((attempt, result):xs) =
                if (take (length attempt) value) == attempt
                    then [(result, drop (length attempt) value)]
                    else tryParse xs

