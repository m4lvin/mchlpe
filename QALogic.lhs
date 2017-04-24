
We now bring questions into the picture, i.e.~into the language.
In order not to go back and change stuff above we start mainly from scratch.

\begin{code}
module QALogic where
\end{code}

There are some bits we can reuse though:

\begin{code}
import AGTYPES (implies,AgentName,Prop,Partition,World,Label)
\end{code}

\subsection{Syntax and Semantics}

Language, Agent Types and Models have to be redefined.

Definition 4: Language PQLTT
\begin{code}
data QForm =
  Top | Prp Prop | AgentName `IsA` AgentType
  | Neg QForm | Conj [QForm]
  | K AgentName QForm
  | Announce AgentName QForm QForm
  | Ask AgentName QForm QForm
  | Answer AgentName QForm
  deriving (Eq,Show)
\end{code}

Abbreviations:
\begin{code}
disj :: [QForm] -> QForm
disj fs = Neg $ Conj (map Neg fs)

impl :: QForm -> QForm -> QForm
impl f g = disj [Neg f, g]

kw :: AgentName -> QForm -> QForm
kw a f = disj [K a f, K a (Neg f)]

-- diamonds
diam :: (QForm -> QForm) -> QForm -> QForm
diam act f = Neg $ act (Neg f)

diamAnnounce :: AgentName -> QForm -> QForm -> QForm
diamAnnounce a f = diam $ Announce a f
\end{code}

We also have to define agent types again because now they map different types of formulas.

\begin{code}
data AgentType = AgT String (AgentName -> QForm -> QForm)
instance (Eq AgentType) where
  (==) (AgT s _) (AgT t _) = s == t
instance (Show AgentType) where
  show (AgT s _) = s

truthTeller, liar, bluffer, subjTruthTeller, subjLiar :: AgentType
truthTeller     = AgT "truthTeller" (const id)
liar            = AgT "liar"        (const Neg)
bluffer         = AgT "bluffer"     (const $ const Top)
subjTruthTeller = AgT "subjTruthTeller" K
subjLiar        = AgT "subjLiar" (\ i f -> Neg $ K i f)

labelAt :: Scene -> Label
labelAt ((ws,_),w) = l where Just (l,_) = lookup w ws

typeAtOf :: Scene -> AgentName -> AgentType
typeAtOf ((ws,_),w) a = t where
  Just (_,tOf) = lookup w ws
  Just t = lookup a tOf

partAtOf :: Scene -> AgentName -> [World]
partAtOf ((_,pss),w) i = head $ filter (elem w) ps where Just ps = lookup i pss

type Model = ( [(World, (Label, [(AgentName, AgentType)]))],
               [(AgentName, Partition World)] )
type Scene = (Model, World)
\end{code}

Definition 5: PQLTT Semantics

\begin{code}
type Context = Maybe (AgentName,QForm)

qIsTrue :: Scene -> Context -> QForm -> Bool
qIsTrue _  _ Top         = True
qIsTrue sc _ (Prp p)     = p `elem` labelAt sc
qIsTrue sc _ (a `IsA` t) = typeAtOf sc a == t
qIsTrue sc c (Neg f)     = not (qIsTrue sc c f)
qIsTrue sc c (Conj fs)   = all (qIsTrue sc c) fs
qIsTrue (m,w) c (K a f)  = all (\v -> qIsTrue (m,v) c f) (partAtOf (m,w) a)
qIsTrue sc _ (Ask a f g) = qIsTrue sc (Just (a,f)) g

qIsTrue _        Nothing         Announce{}        = error "Nobody asked anything!"
qIsTrue sc@(m,w) c@(Just (a1,q)) (Announce a2 f g) =
  (a1 == a2) && f `elem` [q,Neg q] && qCanSay sc a1 f
    `implies` qIsTrue (qAnnounce m c (Just a1) f, w) Nothing g
\end{code}

Note that the semantic clause for answers quantifies over all formulas.
This is not feasible in the implementation as there are infinitely many formulas.
But we know that only the two formulas which count as an answer, i.e.~the formula representing the question and its negation, are relevant.
For all other formulas the Announce-Box will be trivially true
\cite[page 138]{liuWang2013:agentTypesHLPE}.

\begin{code}
qIsTrue sc c (Answer a g) =
  all (\f -> qIsTrue sc c (Announce a f g)) relevantFormulas where
    relevantFormulas = case c of
      Nothing -> []
      Just (_,q) -> [q,Neg q]

qCanSay :: Scene -> AgentName -> QForm -> Bool
qCanSay sc a f = qIsTrue sc Nothing (agtf a f) where AgT _ agtf = typeAtOf sc a

qAnnounce :: Model -> Context -> Maybe AgentName -> QForm -> Model
qAnnounce oldm@(oldws,oldpss) c ma f = (ws,pss) where
  ws = filter check oldws
  check (v,_) = case ma of
    Nothing -> qIsTrue (oldm,v) c f
    Just a -> qIsTrue (oldm,v) Nothing (agtf a f) where AgT _ agtf = typeAtOf (oldm,v) a
  pss = map (fmap strip) oldpss
  strip set = filter ([]/=) $ map (filter (`elem` map fst ws)) set
\end{code}

As usual, validity is truth at all worlds:

\begin{code}
qIsValid :: Model -> QForm -> Bool
qIsValid m f = and [ qIsTrue (m,w) Nothing f | w <- map fst (fst m) ]
\end{code}

% TODO: translations back and forth!

\subsection{Example 5: Death or Freedom with questions}

\begin{code}
example5m1 :: Model
example5m1 =
  ( [ (1,([1],[("A",truthTeller),("B",liar)]))
    , (2,([1],[("A",liar),("B",truthTeller)]))
    , (3,([ ],[("A",truthTeller),("B",liar)]))
    , (4,([ ],[("A",liar),("B",truthTeller)]))
    ], [ ("C", [[1..4]]) ] )

ex5q1, ex5q2 :: QForm -> QForm
-- Will the other man tell me that your path leads to Freedom?
ex5q1 = Ask "A" ( Ask "B" (Prp 1) (diamAnnounce "B" (Prp 1) Top) )
-- Will you say 'yes' if you are asked whether your path leads to Freedom?
ex5q2 = Ask "A" ( Ask "A" (Prp 1) (diamAnnounce "A" (Prp 1) Top) )
-- Both questions ensure that C learns whether Prp 1 holds.
ex5validity :: QForm
ex5validity = Conj [ action $ Answer "A" $ kw "C" (Prp 1) | action <- [ex5q1,ex5q2] ]
\end{code}

Result:
\begin{showCode}
*QALogic> qIsValid example5m1 ex5validity
True
\end{showCode}

% TODO: verify via translations, p. 141

% NEXT: Definition 6, p. 142

% TODO: translate all to PAL, then use symbolic methods???
