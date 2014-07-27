module SymbolTable

data SymbolTable : (n : Nat) -> Nat -> Type -> Type where
  emptySymbolTable : SymbolTable Z Z a
  emptySymbolTableSlot : SymbolTable n missing a -> SymbolTable (S n) (S missing) a
  fullSymbolTableSlot : a -> SymbolTable n missing a -> SymbolTable (S n) missing a

symbolTableToVect : SymbolTable n Z a -> Vect n a
symbolTableToVect emptySymbolTable = []
symbolTableToVect (emptySymbolTableSlot _) impossible
symbolTableToVect (fullSymbolTableSlot x st) = x :: symbolTableToVect st

indexSymbolTable : SymbolTable n Z a -> Fin n -> a
indexSymbolTable st fn = index fn (reverse (symbolTableToVect st))

mapSymbolTable : (a -> b) -> SymbolTable n missing a -> SymbolTable n missing b
mapSymbolTable _ emptySymbolTable = emptySymbolTable
mapSymbolTable f (emptySymbolTableSlot st) = emptySymbolTableSlot (mapSymbolTable f st)
mapSymbolTable f (fullSymbolTableSlot x st) = fullSymbolTableSlot (f x) (mapSymbolTable f st)

fillSymbolTable : a -> SymbolTable n (S missing) a -> SymbolTable n missing a
fillSymbolTable _ emptySymbolTable impossible
fillSymbolTable x (emptySymbolTableSlot st) = fullSymbolTableSlot x st
fillSymbolTable x (fullSymbolTableSlot x' st) = fullSymbolTableSlot x' (fillSymbolTable x st)
