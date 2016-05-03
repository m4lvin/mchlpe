# A Model Checker for the Hardest Logic Puzzle Ever

We implement the logics of Agent Types from [LiuWang2013] in Haskell.
The resulting program checks various Theorems in fractions of seconds.
In particular we verify solutions to the so-called Hardest Logic Puzzle Ever.

The implementation is stand-alone, while similar to DEMO-S5 [vEijck2007].
We make heavy use of Haskell's pattern matching and models are
represented explicitly, using a custom data type based on lists.

Complete literate Haskell documentation is in [mchlpe.pdf](mchlpe.pdf).
