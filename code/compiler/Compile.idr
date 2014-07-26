module Compile

import EmitGCC
import IdrLISP

infixl 1 >>>

compileWith : IdrDeBruijn n ->
              GCC nLabels missing nInstructions ->
              (nLabels' : Nat ** (nInstructions' : Nat ** GCC nLabels' missing nInstructions'))
compileWith (DBVariable x) = ld (finToNat x) Z
compileWith (DBLambda x) = ?compileWithRHS_2
compileWith (DBApp f x) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith f st' of
          (nl' ** (ni' ** st'')) =>
            ap (S Z) st'')

compileWith (DBPrim (Atom k)) = ldc k
compileWith (DBPrim (Cons x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            cons st'')

compileWith (DBPrim (Car x)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) => car st')

compileWith (DBPrim (Cdr x)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) => cdr st')
compileWith (DBPrim (Plus x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            add st'')

compileWith (DBPrim (Times x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            mul st'')

compileWith (DBPrim (Sub x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            sub st'')

compileWith (DBPrim (Div x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            div st'')

compileWith (DBPrim (Eq x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            ceq st'')

compileWith (DBPrim (Leq x y)) =
  (\st =>
    case compileWith y st of
      (nl ** (ni ** st')) =>
        case compileWith x st' of
          (nl' ** (ni' ** st'')) =>
            cgte st'')

compileWith (DBPrim (Lt x y)) =
  (\st =>
    case compileWith y st of
      (nl ** (ni ** st')) =>
        case compileWith x st' of
          (nl' ** (ni' ** st'')) =>
            cgt st'')

compileWith (DBPrim (Gt x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            cgt st'')

compileWith (DBPrim (Geq x y)) =
  (\st =>
    case compileWith x st of
      (nl ** (ni ** st')) =>
        case compileWith y st' of
          (nl' ** (ni' ** st'')) =>
            cgte st'')

compileWith (DBPrim (If x y z)) = ?compileWithRHS_18
compileWith (DBFix x) = ?compileWithRHS_5

compile : IdrDeBruijn Z -> (nLabels' : Nat ** (nInstructions' : Nat ** GCC nLabels' [] nInstructions'))
compile idl = compileWith idl start

compileAndEmit : IdrDeBruijn Z -> String
compileAndEmit idl = case compile idl of
                       (nl ** (ni ** gcc)) => emitGCC gcc
