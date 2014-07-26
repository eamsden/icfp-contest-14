
module Rules (Move(..), legalMove) where

import Board (getB, SubBoard, subB)

data Move = Left | Up | Right | Down
            deriving (Eq, Ord, Show)

legalMove :: Point -> Move -> Board -> Bool
legalMove pt mv bd = inBounds && noCollision

data MoveM a = {isLegal :: SubBoard -> MoveM a}

