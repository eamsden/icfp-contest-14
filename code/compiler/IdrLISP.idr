module IdrLISP

data Prim : Type -> Type where 
  Atom     : Nat -> Prim a
  Cons     : a -> a -> Prim a
  Car      : a -> Prim a
  Cdr      : a -> Prim a
  Plus     : a -> a -> Prim a
  Times    : a -> a -> Prim a
  Sub      : a -> a -> Prim a
  Div      : a -> a -> Prim a
  Eq       : a -> a -> Prim a 
  Leq      : a -> a -> Prim a 
  Lt       : a -> a -> Prim a 
  Gt       : a -> a -> Prim a 
  Geq      : a -> a -> Prim a 
  If       : a -> a -> a -> Prim a

data IdrDeBruijn : Nat -> Type where
  DBVariable : (Fin n) -> IdrDeBruijn n
  DBLambda : IdrDeBruijn (S n) -> IdrDeBruijn n
  DBApp : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
  DBPrim : Prim (IdrDeBruijn n) -> IdrDeBruijn n
  DBFix : IdrDeBruijn n -> IdrDeBruijn n

dsl idrlisp
    lambda = DBLambda
    variable = DBVariable
    index_first = fZ
    index_next = fS

term syntax IF [cond] THEN [consequent] ELSE [alternate] = DBPrim (If cond consequent alternate)

a : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
a = DBApp

fix : IdrDeBruijn n -> IdrDeBruijn n
fix = DBFix

atm : Nat -> IdrDeBruijn n
atm = DBPrim . Atom

cons : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
cons ca cd = DBPrim (Cons ca cd)

car : IdrDeBruijn n -> IdrDeBruijn n
car = DBPrim . Car

cdr : IdrDeBruijn n -> IdrDeBruijn n
cdr = DBPrim . Cdr

plus : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
plus e1 e2 = DBPrim (Plus e1 e2)

times : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
times e1 e2 = DBPrim (Times e1 e2)

sub : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
sub e1 e2 = DBPrim (Sub e1 e2)

div : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
div e1 e2 = DBPrim (Div e1 e2)

eq : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
eq e1 e2 = DBPrim (Eq e1 e2)

lt : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
lt e1 e2 = DBPrim (Lt e1 e2)

leq : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
leq e1 e2 = DBPrim (Leq e1 e2)

geq : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
geq e1 e2 = DBPrim (Geq e1 e2)

gt : IdrDeBruijn n -> IdrDeBruijn n -> IdrDeBruijn n
gt e1 e2 = DBPrim (Gt e1 e2)

