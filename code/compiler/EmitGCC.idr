module EmitGCC

import SymbolTable

infixl 1 #

(#) : a -> (a -> b) -> b
x # f = f x

natToSelfFin : (n : Nat) -> Fin (S n)
natToSelfFin Z = fZ
natToSelfFin (S n) = fS (natToSelfFin n)

data Instr : Nat -> Type where
  LDC : Nat -> Instr nLabels
  LD : Nat -> Nat -> Instr nLabels
  ADD : Instr nLabels
  SUB : Instr nLabels
  MUL : Instr nLabels
  DIV : Instr nLabels
  CEQ : Instr nLabels
  CGT : Instr nLabels
  CGTE : Instr nLabels
  ATOM : Instr nLabels
  CONS : Instr nLabels
  CAR : Instr nLabels
  CDR : Instr nLabels
  SEL : Fin nLabels -> Fin nLabels -> Instr nLabels
  JOIN : Instr nLabels
  LDF : Fin nLabels -> Instr nLabels
  AP : Nat -> Instr nLabels
  RTN : Instr nLabels
  DUM : Nat -> Instr nLabels
  RAP : Nat -> Instr nLabels

emitInstr : SymbolTable nLabels [] nInstructions -> Instr nLabels -> String
emitInstr _  (LDC k) = "LDC  " ++ show k ++ "\n"
emitInstr _  (LD k j) = "LD   " ++ show k ++ " " ++ show j ++ "\n"
emitInstr _  ADD = "ADD\n"
emitInstr _  SUB = "SUB\n"
emitInstr _  MUL = "MUL\n"
emitInstr _  DIV = "DIV\n"
emitInstr _  CEQ = "CEQ\n"
emitInstr _  CGT = "CGT\n"
emitInstr _  CGTE = "CGTE\n"
emitInstr _  ATOM = "ATOM\n"
emitInstr _  CONS = "CONS\n"
emitInstr _  CAR = "CAR\n"
emitInstr _  CDR = "CDR\n"
emitInstr st (SEL x y) = "SEL  " ++ show (finToNat x) ++ " " ++ show (finToNat y) ++ "\n"
emitInstr _  JOIN = "JOIN\n"
emitInstr _  (LDF x) = "LDF  " ++ show (finToNat x) ++ "\n"
emitInstr _  (AP k) = "AP   " ++ show k ++ "\n"
emitInstr _  RTN = "RTN\n"
emitInstr _  (DUM k) = "DUM  " ++ show k ++ "\n"
emitInstr _  (RAP k) = "RAP  " ++ show k ++ "\n"

weakenInstr : Instr n -> Instr (S n)
weakenInstr (LDC n)     = LDC n
weakenInstr (LD n1 n2)  = LD n1 n2
weakenInstr ADD         = ADD
weakenInstr SUB         = SUB
weakenInstr MUL         = MUL
weakenInstr DIV         = DIV
weakenInstr CEQ         = CEQ
weakenInstr CGT         = CGT
weakenInstr CGTE        = CGTE
weakenInstr ATOM        = ATOM
weakenInstr CONS        = CONS
weakenInstr CAR         = CAR
weakenInstr CDR         = CDR
weakenInstr (SEL f1 f2) = SEL (weaken f1) (weaken f2)
weakenInstr JOIN        = JOIN
weakenInstr (LDF f)     = LDF (weaken f)
weakenInstr (AP n)      = AP n
weakenInstr RTN         = RTN 
weakenInstr (DUM n)     = DUM n
weakenInstr (RAP n)     = RAP n

weakenInstrs : Vect nInstrs (Instr nLabels) -> Vect nInstrs (Instr (S nLabels))
weakenInstrs = map weakenInstr

data GCC : Nat -> List Nat -> Nat -> Type where
  mkGCC : SymbolTable nLabels missing (Fin nInstructions) ->
          Vect nInstructions (Instr nLabels) ->
          GCC nLabels missing nInstructions

emitGCC : GCC nLabels [] nInstructions -> String
emitGCC (mkGCC st ins) = concat (map (emitInstr st) (reverse ins))

allocateLabel : GCC nLabels missing nInstructions -> 
                ((fN : Fin (S nLabels)) -> 
                 GCC (S nLabels) (nLabels :: missing) nInstructions ->
                 GCC nLabels' missing' nInstructions') ->
                GCC nLabels' missing' nInstructions'
allocateLabel {nLabels} (mkGCC st ins) f = f (natToSelfFin nLabels) (mkGCC (emptySymbolTableSlot st) (weakenInstrs ins))

data DeleteFromList : List Nat -> Nat -> List Nat -> Type where
  deleteFromHere : DeleteFromList (n :: ns) n ns
  deleteBehind : DeleteFromList as n bs -> DeleteFromList (x :: as) n (x :: bs)

fillLabel : (lab : Fin nLabels) ->
            (pos : Fin nInstructions) ->
            SymbolTable nLabels missing (Fin nInstructions) ->
            {auto d : DeleteFromList missing (finToNat fn) missing'} ->
            SymbolTable nLabels missing' (Fin nInstructions)

placeLabel : (fn : Fin nLabels) ->
             GCC nLabels missing nInstructions ->
             {auto d : DeleteFromList missing (finToNat fn) missing'} ->
             GCC nLabels missing' nInstructions

IC : Nat -> List Nat -> Nat -> Type
IC nLabels missing nInstructions = 
  GCC nLabels missing nInstructions ->
  (nLabels' : Nat ** (nInstructions' : Nat ** GCC nLabels' missing nInstructions'))

appendInstruction : Instr nLabels ->
                    IC nLabels missing nInstructions
appendInstruction i (mkGCC st ins) {nLabels} {nInstructions} =
  (nLabels ** ((S nInstructions) ** mkGCC (mapSymbolTable weaken st) (i :: ins)))

ldc : Nat -> IC nLabels missing nInstructions 
ldc n st = appendInstruction (LDC n) st

ld : Nat -> Nat -> IC nLabels missing nInstructions 
ld n1 n2 = appendInstruction (LD n1 n2)

add : IC nLabels missing nInstructions
add = appendInstruction ADD

sub : IC nLabels missing nInstructions
sub = appendInstruction SUB

mul : IC nLabels missing nInstructions
mul = appendInstruction MUL

div : IC nLabels missing nInstructions
div = appendInstruction DIV

ceq : IC nLabels missing nInstructions
ceq = appendInstruction CEQ

cgt : IC nLabels missing nInstructions
cgt = appendInstruction CGT

cgte : IC nLabels missing nInstructions
cgte = appendInstruction CGTE

atom : IC nLabels missing nInstructions
atom = appendInstruction ATOM

cons : IC nLabels missing nInstructions
cons = appendInstruction CONS

car : IC nLabels missing nInstructions
car = appendInstruction CAR

cdr : IC nLabels missing nInstructions
cdr = appendInstruction CDR

sel : Fin nLabels -> Fin nLabels -> IC nLabels missing nInstructions
sel f1 f2 = appendInstruction (SEL f1 f2)

join : IC nLabels missing nInstructions
join = appendInstruction JOIN

ldf : Fin nLabels -> IC nLabels missing nInstructions
ldf f = appendInstruction (LDF f)

ap : Nat -> IC nLabels missing nInstructions
ap n = appendInstruction (AP n)

rtn : IC nLabels missing nInstructions
rtn = appendInstruction RTN

dum : Nat -> IC nLabels missing nInstructions
dum n = appendInstruction (DUM n)

rap : Nat -> IC nLabels missing nInstructions
rap n = appendInstruction (RAP n)

start : GCC Z [] Z
start = mkGCC emptySymbolTable []
