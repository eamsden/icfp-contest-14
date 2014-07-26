icfp-contest-14
===============

Our approach is to build an EDSL/compiler in Idris to target the GHC/GCC machines.
We will then write a simple AI using probability trees which attempts to avoid getting killed by ghosts,
but offsets scoring opportunities against risks.

File structure

- code/ Code for the compiler and algorithm simulations
- code/compiler/ Idris code for the compiler (ECA)
- code/AIs/ Idris EDSL code for the LambdaMan and Ghost AIs
- code/simulation/ Haskell code for the simulation (SKK)
- solution/ GHC code for ghost AIs and GCC code for the LambdaMan AI

