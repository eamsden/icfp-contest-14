module SymbolTable

data SymbolTable : (n : Nat) -> List Nat -> Type -> Type where
  emptySymbolTable : SymbolTable Z [] a
  emptySymbolTableSlot : SymbolTable n missing a -> SymbolTable (S n) (n :: missing) a
  fullSymbolTableSlot : a -> SymbolTable n missing a -> SymbolTable (S n) missing a

symbolTableToVect : SymbolTable n [] a -> Vect n a
symbolTableToVect emptySymbolTable = []
symbolTableToVect (emptySymbolTableSlot _) impossible
symbolTableToVect (fullSymbolTableSlot x st) = x :: symbolTableToVect st

indexSymbolTable : SymbolTable n [] a -> Fin n -> a
indexSymbolTable st fn = index fn (reverse (symbolTableToVect st))

mapSymbolTable : (a -> b) -> SymbolTable n missing a -> SymbolTable n missing b
mapSymbolTable _ emptySymbolTable = emptySymbolTable
mapSymbolTable f (emptySymbolTableSlot st) = emptySymbolTableSlot (mapSymbolTable f st)
mapSymbolTable f (fullSymbolTableSlot x st) = fullSymbolTableSlot (f x) (mapSymbolTable f st)

