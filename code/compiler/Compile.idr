module Compile

import EmitGCC
import IdrLISP

infixl 1 >>>

compileKont : IdrDeBruijn n ->
              ((nLabels' : Nat) ->
               (missing' : Nat) ->
               (nInstructions' : Nat) ->
               GCC nLabels' missing' nInstructions' ->
               (nLabels'' : Nat ** (nInstructions'' : Nat ** GCC nLabels'' missing' nInstructions''))) ->
              GCC' labelFull nLabels missing nInstructions ->
              (nLabels''' : Nat ** (nInstructions''' : Nat ** GCC nLabels''' missing nInstructions'''))
compileKont (DBVariable x) k gcc {missing} =
  case ld (finToNat x) Z gcc of
    (nLabels' ** (nInstructions' ** gcc')) => k nLabels' missing nInstructions' gcc'

compileKont (DBLambda x) k gcc {missing} = 
  case withLabel
         (\lamLabel, gcc =>
           case ldf lamLabel gcc of
             (nl ** (ni ** gcc')) => k nl (S missing) ni gcc')
         gcc
  of
    (nl ** (ni ** lgcc)) => compileKont x (\nl, m, ni, gcc => rtn gcc) lgcc
      

compileKont (DBApp f x) k gcc = 
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont f
        (\nl, m, ni, gcc=>
          case ap (S Z) gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Atom j)) k gcc {missing} =
  case ldc j gcc of
    (nl ** (ni ** gcc')) => k nl missing ni gcc'
compileKont (DBPrim (Cons x y)) k gcc = 
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case cons gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Car x)) k gcc =
  compileKont x
    (\nl, m, ni, gcc =>
      case car gcc of
        (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
    gcc

compileKont (DBPrim (Cdr x)) k gcc =
  compileKont x
    (\nl, m, ni, gcc =>
      case cdr gcc of
        (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
    gcc

compileKont (DBPrim (Plus x y)) k gcc = 
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case add gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Times x y)) k gcc = 
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case mul gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Sub x y)) k gcc = 
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case sub gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Div x y)) k gcc = 
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case EmitGCC.div gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Eq x y)) k gcc = 
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case ceq gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Leq x y)) k gcc =
  compileKont y
    (\nl, m, ni, gcc =>
      compileKont x
        (\nl, m, ni, gcc =>
          case cgte gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Lt x y)) k gcc =
  compileKont y
    (\nl, m, ni, gcc =>
      compileKont x
        (\nl, m, ni, gcc =>
          case cgt gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Gt x y)) k gcc =
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case cgt gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (Geq x y)) k gcc =
  compileKont x
    (\nl, m, ni, gcc =>
      compileKont y
        (\nl, m, ni, gcc =>
          case cgte gcc of
            (nl' ** (ni' ** gcc')) => k nl' m ni' gcc')
        gcc)
    gcc

compileKont (DBPrim (If cond con alt)) k gcc =
  compileKont cond
    (\ni, m, nl, gcc =>
      case withLabel
             (\consLabel, gcc =>
               case withLabel
                      (\altLabel, gcc => 
                        case sel (weaken consLabel) altLabel gcc of
                          (nl' ** (ni' ** gcc')) => k nl' (S (S m)) ni' gcc')
                      gcc
               of
                 (ni' ** (nl' ** gcc')) => compileKont alt (\nl, m, ni, gcc => join gcc) gcc')
             gcc
      of
        (ni' ** (nl' ** gcc')) => compileKont con (\nl, m, ni, gcc => join gcc) gcc')
    gcc

-- This doesn't work. Figuring out recursive functions will have to happen later
compileKont (DBFix x) k gcc =
  compileKont x
    (\nl, m, ni, gcc =>
      case withLabel
             (\fixLabel, gcc =>
               case dum (S (S Z)) gcc of
                 (nl1 ** (ni ** gcc)) =>
                   case ldf (believe_me fixLabel) gcc of
                     (nl2 ** (ni ** gcc)) =>
                       case ldf (believe_me fixLabel) gcc of
                         (nl3 ** (ni ** gcc)) =>
                           case rap (S (S Z)) gcc of
                             (nl4 ** (ni ** gcc)) =>
                               k nl4 (S m) ni gcc)
           gcc
      of
        (ni ** (nl ** gcc)) =>
          case ld Z (S Z) gcc of
            (ni ** (nl ** gcc)) =>
              case ld Z Z gcc of
                (ni ** (nl ** gcc)) =>
                  case ap (S Z) gcc of
                    (ni ** (nl ** gcc)) =>
                      rtn gcc)
    gcc

compile : IdrDeBruijn Z -> (nLabels' : Nat ** (nInstructions' : Nat ** GCC nLabels' Z nInstructions'))
compile idl = compileKont idl (\nl, m, ni, gcc => rtn gcc) start

compileAndEmit : IdrDeBruijn Z -> String
compileAndEmit idl = case compile idl of
                       (nl ** (ni ** gcc)) => emitGCC gcc

compileEmitAndPrint : IdrDeBruijn Z -> IO ()
compileEmitAndPrint idl = putStr (compileAndEmit idl)
