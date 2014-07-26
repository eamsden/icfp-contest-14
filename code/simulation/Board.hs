
module Board (Board, Point, buildB, putB, getB) where

import Tile (Tile(..))

type Point = (Int, Int)
type Board = [(Point, Char)]

buildB :: [String] -> Board
buildB lns = buildAccB lns 0

buildAccB :: [String] -> Int -> Board 
buildAccB []       _   = []
buildAccB (ln:lns) row = foldr step [] ln ++ buildAccB lns (row + 1)
                             where step c acc = ((row, col acc), c) : acc 
                                   col    acc = length ln - length acc - 1 

putB :: Point -> Char -> Board -> Board
putB findpt newc bd = foldr step [] bd
    where step (pt, oldc) acc | pt == findpt = (pt, newc) : acc
                              | otherwise    = (pt, oldc) : acc

getB :: Point -> Board -> Maybe Char
getB findpt bd = lookup findpt bd

tilB :: Point -> Board -> Tile
tilB findpt bd = read $ case getB findpt bd of
                      Nothing -> show OutBounds
                      Just a  -> [a]


