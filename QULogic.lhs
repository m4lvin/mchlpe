
Additionally to questions, we now also add utterances to our formalism.

\begin{code}
module QULogic where
import Data.Maybe
import HELP (fusion)
import AGTYPES (implies,AgentName,Prop,Partition,World,Label)
\end{code}

Language, Agent Types and Models have to be redefined, again.

\subsection{Syntax}

Definition 6: Language PQLTTU

\begin{code}
type Utterance = String

data QUForm =
  Top | Prp Prop | AgentName `IsA` AgentType
  | Neg QUForm | Conj [QUForm] | Disj [QUForm]
  | Impl QUForm QUForm
  | K AgentName QUForm
  | C [AgentName] QUForm
  | Say AgentName Utterance QUForm
  | Ask AgentName QUForm QUForm
  | Ans AgentName QUForm
  deriving (Eq,Show)
\end{code}

Note that we now also added a common knowledge operator \texttt{C} which is not present in \cite{liuWang2013:agentTypesHLPE}.
We are not interested in the axiomatization of our logic here, hence it easy to deal with.

\begin{code}
vee :: QUForm -> QUForm -> QUForm
vee f g = Disj [f,g]

kw :: AgentName -> QUForm -> QUForm
kw a f = Disj [K a f, K a (Neg f)]

diam :: (QUForm -> QUForm) -> QUForm -> QUForm
diam act f = Neg $ act (Neg f)

diamSay :: AgentName -> Utterance -> QUForm -> QUForm
diamSay a u = diam $ Say a u

diamAns :: AgentName -> QUForm -> QUForm
diamAns a = diam $ Ans a
\end{code}

We also have to define agent types again because now they map different types of formulas.

\begin{code}
data AgentType = AgT String (AgentName -> QUForm -> QUForm)
instance (Eq AgentType) where
  (==) (AgT s _) (AgT t _) = s == t
instance (Show AgentType) where
  show (AgT s _) = s
instance (Ord AgentType) where
  compare (AgT s1 _) (AgT s2 _) = compare s1 s2

truthTeller, liar, bluffer, subjTruthTeller, subjLiar :: AgentType
truthTeller     = AgT "TT" (const id)
liar            = AgT "LL" (const Neg)
bluffer         = AgT "LT" (const $ const Top)
subjTruthTeller = AgT "STT" K
subjLiar        = AgT "SLL" (\ i f -> Neg $ K i f)

type TypeLabel = [(AgentName, AgentType)]

data Meaning = Mng String (QUForm -> QUForm)
instance Show Meaning where
  show (Mng s _) = s
instance Eq Meaning where
  (Mng s1 _) == (Mng s2 _) = s1 == s2
instance Ord Meaning where
  compare (Mng s1 _) (Mng s2 _) = compare s1 s2

type UtteranceLabel = [(Utterance,Meaning)]

data Model = Mo
  [(World, (Label, TypeLabel, UtteranceLabel))]
  [(AgentName, Partition World)]
type Scene = (Model, World)

sizeof :: Model -> Int
sizeof (Mo ws _) = length ws

instance Show Model where
  show (Mo ws pss) =
    concatMap showW ws ++ concatMap showP pss
      where
        showW (w,(ps,ts,us)) = concat
          [ show w, ": ", show ps, ", ", showTS ts, ", ", showUS us, "\n" ]
        showP (a, p) = a ++ ": " ++ show p ++ "\n"
        showT (a, AgT agts _) = a ++ ":" ++ agts
        showTS ts = unwords $ map showT ts
        showU (u, mng) = u ++ "=" ++ show mng
        showUS us = unwords $ map showU us

third :: (a,b,c) -> c
third (_,_,z) = z

labelAt :: Scene -> Label
labelAt (Mo ws _, w) = l where Just (l,_,_) = lookup w ws

typeAtOf :: Scene -> AgentName -> AgentType
typeAtOf (Mo ws _, w) a = t where
  Just (_,tOf,_) = lookup w ws
  Just t = lookup a tOf

meaningAtOfGiven :: Scene -> Utterance -> Meaning
meaningAtOfGiven (Mo ws _, w) u = m where
  val = fromMaybe
    (error $ "World " ++ show w ++ " disappeared!" ++ show ws)
    (lookup w ws)
  Just m = lookup u (third val)

meanfctAtOfGiven :: Scene -> Utterance -> QUForm -> QUForm
meanfctAtOfGiven sc u = mngf where
  Mng _ mngf = meaningAtOfGiven sc u

partOf :: Model -> AgentName -> Partition World
partOf (Mo _ pss) i = ps where Just ps = lookup i pss

partAtOf :: Scene -> AgentName -> [World]
partAtOf (Mo _ pss, w) i = head $ filter (elem w) ps where
  Just ps = lookup i pss
\end{code}

\subsection{Semantics}

Definition 7: PQLTTU Semantics (p. 142)
\begin{code}
type Context = Maybe (AgentName,QUForm)

qIsTrue :: Scene -> Context -> QUForm -> Bool
qIsTrue _  _ Top         = True
qIsTrue sc _ (Prp p)     = p `elem` labelAt sc
qIsTrue sc _ (a `IsA` t) = typeAtOf sc a == t
qIsTrue sc c (Neg f)     = not (qIsTrue sc c f)
qIsTrue sc c (Conj fs)   = all (qIsTrue sc c) fs
qIsTrue sc c (Disj fs)   = any (qIsTrue sc c) fs
qIsTrue sc c (Impl f g)  = not (qIsTrue sc c f) || qIsTrue sc c g
qIsTrue (m,w) c (K a f)  = all (\v -> qIsTrue (m,v) c f) (partAtOf (m,w) a)
qIsTrue (m,w) c (C as f) = all (\v -> qIsTrue (m,v) c f) vs where
  vs    = head $ filter (elem w) ckrel
  ckrel = fusion $ concat [ partOf m i | i <- as ]
\end{code}

Note that the last clause is not in \cite{liuWang2013:agentTypesHLPE}.
As usual we interpret common knowledge as the transitive closure of the union of the epistemic relations of a set of agents. Because these relations are represented as partitions we use the \texttt{fusion} function from \cite{JvE2014:EREL}.

\begin{code}
qIsTrue sc       _               (Ask a f g)    = qIsTrue sc (Just (a,f)) g
qIsTrue _        Nothing         Say{}          = error "Nobody asked anything!"
qIsTrue sc@(m,w) c@(Just (a1,q)) (Say a2 u phi) =
  (a1 == a2) && f `elem` [q,Neg q] && qCanSay sc a1 f
    `implies` qIsTrue (qAnnounce m c a1 u, w) Nothing phi
  where
    f = meanfctAtOfGiven sc u q
\end{code}

Now the last clause quantifies over all utterances.
This is easier to deal with than the quantifier over all formulas above:
  The model gives us a list of all interpretable utterances.

\begin{code}
qIsTrue sc@(m,_) c (Ans a phi) =
  all (\u -> qIsTrue sc c (Say a u phi)) relevantUtterances where
    relevantUtterances :: [Utterance]
    relevantUtterances = case c of
      Nothing -> []
      Just _  -> allUtterances m
    allUtterances (Mo ws _) = map fst $ third $ snd $ head ws

qCanSay :: Scene -> AgentName -> QUForm -> Bool
qCanSay sc a f = qIsTrue sc Nothing (agtf a f) where AgT _ agtf = typeAtOf sc a
\end{code}

The function to restrict a model now takes an utterance, not a formula as argument.
This is important because the utterance can have different meanings in other worlds in which case also the formula giving the condition whether the world is kept or deleted differs from the one at the actual world.

\begin{code}
qAnnounce :: Model -> Context -> AgentName -> Utterance -> Model
qAnnounce oldm@(Mo oldws oldpss) c a u = Mo ws pss where
  ws = filter check oldws
  check (v,_) = qIsTrue (oldm,v) Nothing (agtf a f) where
    AgT _ agtf = typeAtOf (oldm,v) a
    f = meanfctAtOfGiven (oldm,v) u q
    Just (_,q) = c
  pss = map (fmap strip) oldpss
  strip set = filter ([]/=) $ map (filter (`elem` map fst ws)) set
\end{code}

Validity is truth at all worlds:
\begin{code}
qIsValid :: Model -> QUForm -> Bool
qIsValid m@(Mo ws _) f = and [ qIsTrue (m,w) Nothing f | w <- map fst ws ]
\end{code}

\subsection{Questioning Strategies, Puzzles and Solutions}

Definition 8: Questioning Strategy (p. 143)

We define a question as a pair of an agent and a formula. A
questioning strategy is a directed graph where the nodes are
questions and the edges are labeled with utterances.

As in the paper we only use strategies which are directed acyclic
graphs (DAGs) here. Thus a strategy is either a final state (stop
asking) or a question state which comes with the information whom to
ask what and a map of utterances to follow-up strategies (what to do
next, depending on the utterance).

\begin{code}
type Question = (AgentName,QUForm)
type Answer = Utterance
data Strategy = FState | QState Question [(Utterance,Strategy)] deriving (Eq)

instance Show Strategy where
  show = myshow "" where
    myshow space FState = space ++ "Stop.\n"
    myshow space (QState (a,f) branches) =
      space ++ "Ask " ++ a ++ " if >>" ++ show f ++ "<<.\n"
        ++ concatMap linesFor branches
      where
        linesFor (u,FState) = space ++ "  If they say '" ++ show u ++ "', then stop.\n"
        linesFor (u,nexts ) = space ++ "  If they say '" ++ show u ++ "', then:\n"
          ++ myshow (space ++ "    ") nexts
\end{code}

\begin{code}
type Sequence = [(Question,Answer)]

sequencesOf :: Strategy -> [Sequence]
sequencesOf FState = [ [] ]
sequencesOf (QState q branches) =
  concatMap (\(u,next) -> [(q,u):rest | rest <- sequencesOf next]) branches
\end{code}

A puzzle is a pair $(M,\theta)$ of a model which describes the initial situation and a formula which states the goal to be reached.
It is solved by a strategy $S$ iff for all sequences $s$ of $S$ we have that $M \vDash \phi_s^\theta$.
Here $\phi_s^\theta$ is the formula saying that all reachable questions in $s$ can be answered and after the whole sequence is executed $\theta$ holds.

\begin{code}
type Puzzle = (Model,QUForm)

solves :: Strategy -> Puzzle -> Bool
solves strategy (m,goal) = all
  (qIsValid m . seq2f goal)
  (sequencesOf strategy)

seq2f :: QUForm -> Sequence -> QUForm
seq2f goal (((a,q),u):rest) =
  Ask a q $                        -- After asking a whether q,
    Conj [ diamAns a Top           --   a can answer somehow and
          , Say a u $ seq2f goal rest ] --   after a says u ...
seq2f goal [] = goal               -- ... the goal formula is true.
\end{code}

If the questions in a strategy are always answerable, the check whether a strategy solves a puzzle can be simplified by leaving out \texttt{diamAns a Top}.

\begin{code}
solvesSimple :: Strategy -> Puzzle -> Bool -- p. 144
solvesSimple strategy (model,goal) = all okay (sequencesOf strategy) where
  okay qaSeq = qIsValid model (seq2fSimple qaSeq)
  seq2fSimple [] = goal
  seq2fSimple (((a,q),u):rest) = Ask a q $ Say a u $ seq2fSimple rest
\end{code}
