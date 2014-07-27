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

emitInstr : SymbolTable nLabels Z (Fin nInstructions) -> Instr nLabels -> String
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
emitInstr st (SEL x y) = "SEL  " ++ show (finToNat (indexSymbolTable st x)) ++ " " ++ show (finToNat (indexSymbolTable st y)) ++ "\n"
emitInstr _  JOIN = "JOIN\n"
emitInstr st (LDF x) = "LDF  " ++ show (finToNat (indexSymbolTable st x)) ++ "\n"
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

data GCC' : Bool -> Nat -> Nat -> Nat -> Type where
  mkGCCEndLabel : SymbolTable nLabels missing (Fin (S nInstructions)) ->
                  Vect nInstructions (Instr nLabels) ->
                  GCC' False nLabels missing nInstructions
  mkGCC : SymbolTable nLabels missing (Fin nInstructions) ->
          Vect nInstructions (Instr nLabels) ->
          GCC' True nLabels missing nInstructions
         
GCC : Nat -> Nat -> Nat -> Type
GCC = GCC' True

emitGCC : GCC nLabels Z nInstructions -> String
emitGCC (mkGCC st ins) = concat (map (emitInstr st) (reverse ins))

withLabel : (Fin (S nLabels) ->
             GCC' labelFull (S nLabels) (S missing) nInstructions ->
             (nLabels' : Nat ** (nInstructions' : Nat ** GCC nLabels' (S missing) nInstructions'))) ->
            GCC' labelFull nLabels missing nInstructions ->
            (nLabels'' : Nat ** (nInstructions'' : Nat ** GCC' False nLabels'' missing nInstructions''))
withLabel {nLabels} f (mkGCC st is) =
  case f (natToSelfFin nLabels) (mkGCC (emptySymbolTableSlot st) (weakenInstrs is)) of
    (nl ** (ni ** (mkGCC st' is'))) => (nl ** (ni ** (mkGCCEndLabel (fillSymbolTable (natToSelfFin ni) (mapSymbolTable weaken st')) is')))
withLabel {nLabels} f (mkGCCEndLabel st is) =
  case f (natToSelfFin nLabels) (mkGCCEndLabel (emptySymbolTableSlot st) (weakenInstrs is)) of
    (nl ** (ni ** (mkGCC st' is'))) => (nl ** (ni ** (mkGCCEndLabel (fillSymbolTable (natToSelfFin ni) (mapSymbolTable weaken st')) is')))

IC : Bool -> Nat -> Nat -> Nat -> Type
IC labelFull nLabels missing nInstructions = 
  GCC' labelFull nLabels missing nInstructions ->
  (nLabels' : Nat ** (nInstructions' : Nat ** GCC nLabels' missing nInstructions'))

appendInstruction : Instr nLabels ->
                    IC labelFull nLabels missing nInstructions
appendInstruction i (mkGCCEndLabel st ins) {nLabels} {nInstructions} =
  (nLabels ** ((S nInstructions) ** mkGCC st (i :: ins)))
appendInstruction i (mkGCC st ins) {nLabels} {nInstructions} =
  (nLabels ** ((S nInstructions) ** mkGCC (mapSymbolTable weaken st) (i :: ins)))

ldc : Nat -> IC labelFull nLabels missing nInstructions 
ldc n st = appendInstruction (LDC n) st

ld : Nat -> Nat -> IC labelFull nLabels missing nInstructions 
ld n1 n2 = appendInstruction (LD n1 n2)

add : IC labelFull nLabels missing nInstructions
add = appendInstruction ADD

sub : IC labelFull nLabels missing nInstructions
sub = appendInstruction SUB

mul : IC labelFull nLabels missing nInstructions
mul = appendInstruction MUL

div : IC labelFull nLabels missing nInstructions
div = appendInstruction DIV

ceq : IC labelFull nLabels missing nInstructions
ceq = appendInstruction CEQ

cgt : IC labelFull nLabels missing nInstructions
cgt = appendInstruction CGT

cgte : IC labelFull nLabels missing nInstructions
cgte = appendInstruction CGTE

atom : IC labelFull nLabels missing nInstructions
atom = appendInstruction ATOM

cons : IC labelFull nLabels missing nInstructions
cons = appendInstruction CONS

car : IC labelFull nLabels missing nInstructions
car = appendInstruction CAR

cdr : IC labelFull nLabels missing nInstructions
cdr = appendInstruction CDR

sel : Fin nLabels -> Fin nLabels -> IC labelFull nLabels missing nInstructions
sel f1 f2 = appendInstruction (SEL f1 f2)

join : IC labelFull nLabels missing nInstructions
join = appendInstruction JOIN

ldf : Fin nLabels -> IC labelFull nLabels missing nInstructions
ldf f = appendInstruction (LDF f)

ap : Nat -> IC labelFull nLabels missing nInstructions
ap n = appendInstruction (AP n)

rtn : IC labelFull nLabels missing nInstructions
rtn = appendInstruction RTN

dum : Nat -> IC labelFull nLabels missing nInstructions
dum n = appendInstruction (DUM n)

rap : Nat -> IC labelFull nLabels missing nInstructions
rap n = appendInstruction (RAP n)

start : GCC Z Z Z
start = mkGCC emptySymbolTable []
