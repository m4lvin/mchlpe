
\begin{code}
module HLPE where

import Control.Arrow
import Data.List
import HELP ((!))

import AGTYPES (AgentName)
import QULogic
\end{code}

\subsection{Formalizing HLPE}

We are now on page 145.

\begin{code}
allTypes :: [AgentType]
allTypes = [truthTeller,liar,bluffer]

allAgents :: [AgentName]
allAgents = ["A","B","C","D"]

knights :: [AgentName]
knights = ["A","B","C"]

jaInt,daInt :: UtteranceLabel
jaInt = [("ja", Mng "yes" id), ("da", Mng "no" Neg)]
daInt = [("ja", Mng "no" Neg), ("da", Mng "yes" id)]

m0 :: Model
m0 = Mo
    (zip [1..] allVals)
    [ ("A", knowAll), ("B", knowAll), ("C", knowAll), ("D", knowNothing)]
  where
    typeLists = permutations [truthTeller,liar,bluffer]
    agLabelFor [at,bt,ct] = [("A",at), ("B",bt), ("C",ct), ("D",truthTeller)]
    -- the paper does not give a type to "D" but it is needed to evaluate phiE5
    agLabelFor _ = error "this will never happen."
    allVals = [ ([],agLabelFor ats,uLabel) | uLabel <- [jaInt,daInt], ats <- typeLists ]
    knowAll = map return [1..(length allVals)]
    knowNothing = [ [1..(length allVals)] ]
\end{code}

\begin{showCode}
*QULogic GOA> m0
1:  [], A:TT B:LL C:LT D:TT, ja=yes da=no
2:  [], A:LL B:TT C:LT D:TT, ja=yes da=no
3:  [], A:LT B:LL C:TT D:TT, ja=yes da=no
4:  [], A:LL B:LT C:TT D:TT, ja=yes da=no
5:  [], A:LT B:TT C:LL D:TT, ja=yes da=no
6:  [], A:TT B:LT C:LL D:TT, ja=yes da=no
7:  [], A:TT B:LL C:LT D:TT, ja=no  da=yes
8:  [], A:LL B:TT C:LT D:TT, ja=no  da=yes
9:  [], A:LT B:LL C:TT D:TT, ja=no  da=yes
10: [], A:LL B:LT C:TT D:TT, ja=no  da=yes
11: [], A:LT B:TT C:LL D:TT, ja=no  da=yes
12: [], A:TT B:LT C:LL D:TT, ja=no  da=yes
A: [[1],[2],[3],[4],[5],[6],[7],[8],[9],[10],[11],[12]]
B: [[1],[2],[3],[4],[5],[6],[7],[8],[9],[10],[11],[12]]
C: [[1],[2],[3],[4],[5],[6],[7],[8],[9],[10],[11],[12]]
D: [[1,2,3,4,5,6,7,8,9,10,11,12]]
\end{showCode}

\subsection{Formalizing and checking the modelling assumptions}

\begin{code}
phiE1, phiE2, phiE3, phiE4, phiE5 :: QUForm
-- A, B and C are of different types and this is common knowledge.
phiE1 = C allAgents knightsDiff where
  knightsDiff = Conj [ differentTs a1 a2 | a1 <- knights, a2 <- delete a1 knights ]
  differentTs a1 a2 = Conj [ (a1 `IsA` t) `Impl` (Neg $ a2 `IsA` t) | t <- allTypes ]
-- A, B and C know each other's type and this is common knowledge.
phiE2 = C allAgents knightsKnow where
  knightsKnow = Conj [ a1 `knowsTypeOf` a2 | a1 <- knights, a2 <- knights ]
  knowsTypeOf a1 a2 = Disj [ K a1 (a2 `IsA` t) | t <- allTypes ]
-- A, B and C know the meaning of 'da' and 'ja' and this is common knowledge.
phiE3 = C allAgents knightsKnow where
  knightsKnow = Conj [ Disj [ K k jaMeansYes, K k daMeansYes ] | k <- knights ]
-- D does not know the types of A, B, C and this is common knowledge.
phiE4 = C allAgents $ Conj
  [ Neg $ K "D" (k `IsA` t) | k <- ["A","B","C"], t <- allTypes ]
-- D does not know the meanings of 'da; and 'ja' but he knows that one
-- means 'yes' and the other means 'no', and this is common knowledge.
phiE5 = C allAgents $ Conj
  [ K "D" $ Disj [ jaMeansYes, daMeansYes ]
  , Neg $ Disj [ K "D" jaMeansYes, K "D" daMeansYes ] ]

jaMeansYes :: QUForm
jaMeansYes = Conj (map phiJA allAgents) where
  phiJA x = (x `IsA` truthTeller) `Impl` Conj
    [ Ask x (      x `IsA` truthTeller) $ diamSay x "ja" Top
    , Ask x (Neg $ x `IsA` truthTeller) $ diamSay x "da" Top ]

daMeansYes :: QUForm
daMeansYes = Conj (map phiDA allAgents) where
  phiDA x = (x `IsA` truthTeller) `Impl` Conj
    [ Ask x (      x `IsA` truthTeller) $ diamSay x "da" Top
    , Ask x (Neg $ x `IsA` truthTeller) $ diamSay x "ja" Top ]
\end{code}

Check that the model m0 satisfies all the modelling assumptions:
\begin{showCode}
*QULogic GOA> qIsValid m0 (Conj [phiE1,phiE2,phiE3,phiE4,phiE5])
True
\end{showCode}

We can now define the HLPE itself:
\begin{code}
hlpe :: Puzzle
hlpe = (m0, chi) where
  chi = Conj [ Disj [ K "D" (a `IsA` t) | t <- allTypes ] | a <- knights ]
\end{code}

The $E^\ast$ operator:
\begin{code}
eStar :: AgentName -> QUForm -> QUForm
eStar a f = Ask a f $ diamSay a "ja" Top
\end{code}

\subsection{Checking the Rabern Strategy}

On page page 147 of \cite{liuWang2013:agentTypesHLPE} we find the
following formula, describing how $D$ can learn something no matter
how $B$ answers the nested question.

\begin{code}
checkHint :: QUForm
checkHint = Ask "B"
  (Ask "B" ("A" `IsA` bluffer) $ diamSay "B" "ja" Top)
  (Conj
    [ Say "B" "ja" $ K "D" ( (Neg $ "B" `IsA` bluffer) `Impl` ("A" `IsA` bluffer) )
    , Say "B" "da" $ K "D" ( (Neg $ "B" `IsA` bluffer) `Impl` (Neg $ "A" `IsA` bluffer) ) ])
\end{code}

\begin{showCode}
*QULogic GOA> qIsValid m0 checkHint
True
\end{showCode}


The strategy from Rabern and Rabern \cite{rabern2008simple}, as formalized on page 148 of \cite{liuWang2013:agentTypesHLPE}.

\begin{code}
rabern :: Strategy
rabern =
  QState q1
    [ ("ja", QState q2c [ (u, QState q3c stop ) | u <- [ "ja", "da" ] ] )
    , ("da", QState q2a [ (u, QState q3a stop ) | u <- [ "ja", "da" ] ] ) ]
  where
    -- First ask B to find out whether A or C is a non-bluffer:
    q1  = ("B", eStar "B" ("A" `IsA` bluffer))
    -- Now ask the non-bluffer about the other two:
    q2c = ("C", eStar "C" ("C" `IsA` truthTeller))
    q3c = ("C", eStar "C" ("B" `IsA` bluffer))
    q2a = ("A", eStar "A" ("A" `IsA` truthTeller))
    q3a = ("A", eStar "A" ("B" `IsA` bluffer))
    stop = [ (u, FState) | u <- [ "ja", "da" ] ]
\end{code}

\begin{showCode}
*QULogic> solves rabern hlpe
True
\end{showCode}

\subsection{Replacing gods with ordinary people}

We now implement Example 6: HLPE with ignorance.

\begin{code}
allSubjTypes :: [AgentType]
allSubjTypes = [subjTruthTeller,subjLiar,bluffer]

phiE0',phiE1',phiE2',phiE3',phiE4',phiE5' :: QUForm
-- A, B and C are of types STT,SLL,LT and this is common knowledge (atick).
phiE0' = C allAgents $ Conj (map someoneIs allSubjTypes) where
  someoneIs t = Disj [ a `IsA` t | a <- knights ]
-- A, B and C are of different types atick.
-- (This is the same as phiE1 above, but redefined here for the subjective types.
--  Could be avoided if we had a primitive operator for "have different types")
phiE1' = C allAgents knightsDiff where
  knightsDiff = Conj [ differentTs a1 a2 | a1 <- knights, a2 <- delete a1 knights ]
  differentTs a1 a2 = Conj [ (a1 `IsA` t) `Impl` (Neg $ a2 `IsA` t) | t <- allSubjTypes ]
-- A, B and C know their own types but do not know others' types, atick.
phiE2' = C allAgents $ Conj $ map knowSelf knights ++ map notknowOthers knights where
  knowSelf a = Disj [ K a (a `IsA` t) | t <- allSubjTypes ]
  notknowOthers a = Conj [Neg $ Disj [ K a (b `IsA` t) | t <- allSubjTypes ] | b <- delete a knights]
-- A, B and C know the meaning of 'da' and 'ja' and this is common knowledge.
phiE3' = phiE3
-- D does not know the types of A, B, C and this is common knowledge.
phiE4' = C allAgents $ Conj
  [ Neg $ K "D" (k `IsA` t) | k <- ["A","B","C"], t <- allSubjTypes ]
-- D does not know the meanings of 'da; and 'ja' but he knows that one
-- means 'yes' and the other means 'no', and this is common knowledge.
phiE5' = C allAgents $ Conj
  [ K "D" $ Disj [ jaMeansYes, daMeansYes ]
  , Neg $ Disj [ K "D" jaMeansYes, K "D" daMeansYes ] ]

\end{code}

Then we define the new model $M_1$ as follows.

\begin{code}
m1 :: Model
m1 = Mo states (map (\c -> ([c],relFor [c])) "ABCD")
  where
    typeLists = permutations allSubjTypes
    agLabelFor [at,bt,ct] = [("A",at), ("B",bt), ("C",ct), ("D",truthTeller)]
    agLabelFor _ = error "this will never happen."
    allVals = [ ([],agLabelFor ats,uLabel) | uLabel <- [jaInt,daInt], ats <- typeLists ]
    states = zip [1..] allVals
    relFor "D" = [ [1..(length allVals)] ] -- knows nothing
    relFor a = sort $ map (map fst) $ groupBy same (sortOn sortpick states) where
      same (_,(_,sTl,sUl)) (_,(_,tTl,tUl)) = sTl!a == tTl!a && sUl == tUl
      sortpick (_,(_,sTl,sUl)) =  (sUl,sTl!a)
\end{code}

\begin{showCode}
*QULogic GOA> m1
1:  [], A:TT B:LL C:LT D:TT, ja=yes da=no
2:  [], A:LL B:TT C:LT D:TT, ja=yes da=no
3:  [], A:LT B:LL C:TT D:TT, ja=yes da=no
4:  [], A:LL B:LT C:TT D:TT, ja=yes da=no
5:  [], A:LT B:TT C:LL D:TT, ja=yes da=no
6:  [], A:TT B:LT C:LL D:TT, ja=yes da=no
7:  [], A:TT B:LL C:LT D:TT, ja=no  da=yes
8:  [], A:LL B:TT C:LT D:TT, ja=no  da=yes
9:  [], A:LT B:LL C:TT D:TT, ja=no  da=yes
10: [], A:LL B:LT C:TT D:TT, ja=no  da=yes
11: [], A:LT B:TT C:LL D:TT, ja=no  da=yes
12: [], A:TT B:LT C:LL D:TT, ja=no  da=yes
A: [[1,6],[2,4],[3,5],[7,12],[8,10],[9,11]]
B: [[1,3],[2,5],[4,6],[7,9],[8,11],[10,12]]
C: [[1,2],[3,4],[5,6],[7,8],[9,10],[11,12]]
D: [[1,2,3,4,5,6,7,8,9,10,11,12]]
\end{showCode}

And check that it satisfies all the modelling assumptions:

\begin{showCode}
*QULogic GOA> all (qIsValid m1) [phiE0', phiE1', phiE2', phiE3', phiE4', phiE5']
True
\end{showCode}

We can now check the formula from page 150 to see that Lemma 1 does not hold on \texttt{m1}.

\begin{code}
lemma1broken :: QUForm
lemma1broken = Ask "A"
  (Ask "A" ("B" `IsA` bluffer) $ diamSay "A" "ja" Top)
  (Say "A" "da" $
    K "D" ( (Neg $ "A" `IsA` bluffer) `Impl` (Neg $ "B" `IsA` bluffer) ) )
\end{code}

\begin{showCode}
*Explain GOA> qIsValid m0 lemma1broken
True
*Explain GOA> qIsValid m1 lemma1broken
False
\end{showCode}

We now define the unsolvable puzzles from page 151. Note that our
program provides no way of checking that there is no solution. One
way to realize this would be to introduce an "arbitrary question"
operator, saying "there is a question after which ...".

\begin{code}
subjUnsolvableHlpe :: Puzzle
subjUnsolvableHlpe = (m2,goal) where
  goal = Conj (map theta knights) where
    theta a = Disj [ K "D" (a `IsA` t) | t <- allSubjTypes ]
\end{code}

However, the following more modest goal is reachable.

\begin{code}
subjGoal' :: QUForm
subjGoal' = Disj (map theta' knights) where
  theta' a = Disj [ K "D" (a `IsA` t) | t <- [subjLiar,subjTruthTeller] ]
\end{code}

Defining m2 as the upper part of m1:

\begin{code}
m2 :: Model
m2 = Mo newstates newrel where
  Mo oldstates oldrel = m1
  newstates = filter (\(_,(_,_,ulabel)) -> jaInt==ulabel) oldstates
  newrel = map (second restrict) oldrel
  restrict r = filter (not.null) $ map (filter (`elem` map fst newstates)) r
\end{code}

The model looks as follows and it is easy to verify that the meaning
of "ja" is common knowledge here.

\begin{showCode}
*QULogic GOA> m2
1: [], A:STT B:SLL C:LT  D:TT, ja=yes da=no
2: [], A:SLL B:STT C:LT  D:TT, ja=yes da=no
3: [], A:LT  B:SLL C:STT D:TT, ja=yes da=no
4: [], A:SLL B:LT  C:STT D:TT, ja=yes da=no
5: [], A:LT  B:STT C:SLL D:TT, ja=yes da=no
6: [], A:STT B:LT  C:SLL D:TT, ja=yes da=no
A: [[1,6],[2,4],[3,5]]
B: [[1,3],[2,5],[4,6]]
C: [[1,2],[3,4],[5,6]]
D: [[1,2,3,4,5,6]]

*QULogic GOA> qIsValid m2 (C allAgents jaMeansYes)
True
\end{showCode}

The solution from page 152 is to as ask each of A, B and C "Are you a bluffer".
In this strategy the answers do not matter to which question is asked next.
The following code highlights this with the infix function \texttt{anyway}.
Moreover, we can also check the strategy with nested question to reach the goal on m1.

\begin{code}
m2strat :: Strategy
m2strat = ask "A" `anyway` ( ask "B" `anyway` ( ask "C" `anyway` FState ) ) where
  anyway q s = QState q [ (u,s) | u <- [ "ja", "da" ] ]
  ask i  = (i, i `IsA` bluffer)

m1strat :: Strategy
m1strat = ask "A" `anyway` ( ask "B" `anyway` ( ask "C" `anyway` FState ) ) where
  anyway q s = QState q [ (u,s) | u <- [ "ja", "da" ] ]
  ask i  = (i, nest i (i `IsA` bluffer))
  nest i psi = Ask i
    (Conj [ i `IsA` subjTruthTeller `Impl` psi, i `IsA` subjLiar `Impl` Neg psi])
    (diamSay i "ja" Top)
\end{code}

\begin{showCode}
*QULogic GOA> m2strat `solves` (m2,subjGoal')
True
*QULogic GOA> m1strat `solves` (m1,subjGoal')
True
\end{showCode}
