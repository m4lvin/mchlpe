# A Model Checker for the Hardest Logic Puzzle Ever

## Abstract

We implement the logics of Agent Types from [LiuWang2013] in Haskell.
The resulting program checks various Theorems in fractions of seconds.
In particular we verify a solution [Rabern2008] to the so-called
Hardest Logic Puzzle Ever.

The implementation is stand-alone, while similar to DEMO-S5 [vEijck2007].
We make heavy use of Haskell's pattern matching and models are
represented explicitly, using a custom data type based on lists.

Complete literate Haskell documentation is in [mchlpe.pdf](mchlpe.pdf).

Slides from a talk at [PhDs in Logic VIII](http://www.mathematik.tu-darmstadt.de/fbereiche/logik/phdsinlogic2016)
are [here](https://w4eg.de/malvin/illc/2016-05-10-mchlpe-talk-darmstadt.pdf).


## References

[LiuWang2013] Fenrong Liu and Yanjing Wang:
*Reasoning About Agent Types and the Hardest Logic Puzzle Ever*.
In: *Minds and Machines* Vol. 23, 2013.
[doi:10.1007/s11023-012-9287-x](https://doi.org/10.1007/s11023-012-9287-x)

[vEijck2007] Jan van Eijck: *DEMO-S5*.
Tehnical Report, 2014.
<https://homepages.cwi.nl/~jve/software/demo_s5/>

[Rabern2008] Brian Rabern and Landon Rabern:
*A Simple Solution to the Hardest Logic Puzzle Ever*.
In: *Analysis* Vol. 68, 2008.
[doi:10.1093/analys/68.2.105](https://doi.org/10.1093/analys/68.2.105)


## Obligatory XKCDs

[![xkcd: Labyrinth Puzzle](https://imgs.xkcd.com/comics/labyrinth_puzzle.png)](https://xkcd.com/246/)

[![xkcd: Automation](https://imgs.xkcd.com/comics/automation.png)](https://xkcd.com/1319/)
