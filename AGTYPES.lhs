
\begin{code}
module AGTYPES where

type Prop = Int
type AgentName = String
\end{code}

An agent type is a function which takes an agent name and a formula as arguments and returns a formula.
The returned formula is the precondition for an agent to announce the given formula.
Additionally our data type \texttt{AgentType} contains a string to allow equality checks.
\begin{code}
data AgentType = AgT String (AgentName -> Form -> Form)
instance (Eq AgentType) where (==) (AgT s _) (AgT t _) = s == t
instance (Show AgentType) where show (AgT s _) = s

truthTeller, liar, bluffer, subjTruthTeller, subjLiar :: AgentType
truthTeller     = AgT "truthTeller" (const id)
liar            = AgT "liar"        (const Neg)
bluffer         = AgT "bluffer"     (const $ const Top)
subjTruthTeller = AgT "subjTruthTeller" K
subjLiar        = AgT "subjLiar" (\ i f -> Neg $ K i f)
\end{code}

\subsection{Syntax and Semantics}

Definition 2: Language
\begin{code}
data Form =
  Top | Prp Prop | AgentName `IsA` AgentType
  | Neg Form | Conj [Form]
  | K AgentName Form
  | Announce AgentName Form Form
  | GodAnnounce Form Form
  deriving (Eq,Show)
\end{code}

Abbreviations:
\begin{code}
disj :: [Form] -> Form
disj fs = Neg $ Conj (map Neg fs)
impl :: Form -> Form -> Form
impl f g = disj [Neg f, g]

kw :: AgentName -> Form -> Form
kw a f = disj [K a f, K a (Neg f)]

diamAnnounce :: AgentName -> Form -> Form -> Form
diamAnnounce a f g = Neg $ Announce a f (Neg g)
\end{code}

Definition 3: $\texttt{PALT}^\texttt{T}$ Models and Semantics
\begin{code}
type World = Int
type Partition a = [[a]]
type Label = [Prop]
type Model = ( [(World, (Label, [(AgentName, AgentType)]))],
               [(AgentName, Partition World)] )
type Scene = (Model, World)

labelAt :: Scene -> Label
labelAt ((ws,_),w) = l where Just (l,_) = lookup w ws

typeAtOf :: Scene -> AgentName -> AgentType
typeAtOf ((ws,_),w) a = t where
  Just (_,tOf) = lookup w ws
  Just t = lookup a tOf

partAtOf :: Scene -> AgentName -> [World]
partAtOf ((_,pss),w) i = head $ filter (elem w) ps
  where Just ps = lookup i pss

implies :: Bool -> Bool -> Bool
implies a b = not a || b

isTrue :: Scene -> Form -> Bool
isTrue _  Top         = True
isTrue sc (Prp p)     = p `elem` labelAt sc
isTrue sc (a `IsA` t) = typeAtOf sc a == t
isTrue sc (Neg f)     = not $ isTrue sc f
isTrue sc (Conj fs)   = all (isTrue sc) fs
isTrue (m,w) (K a f)  = all (\v -> isTrue (m,v) f) (partAtOf (m,w) a)
isTrue sc@(m,w) (Announce a f g) =
  canSay sc a f `implies` isTrue (announce m (Just a) f, w) g
isTrue sc@(m,w) (GodAnnounce f g) =
  isTrue sc f `implies` isTrue (announce m Nothing f, w) g

canSay :: Scene -> AgentName -> Form -> Bool
canSay sc a f = isTrue sc (agtf a f) where AgT _ agtf = typeAtOf sc a
\end{code}

Announcement: Given a model, let agent $a$ announce $f$.
If no $a$ is given, let god announce it.
\begin{code}
announce :: Model -> Maybe AgentName -> Form -> Model
announce oldm@(oldws,oldpss) ma f = (ws,pss) where
  ws = filter check oldws
  check (v,_) = case ma of
    Nothing -> isTrue (oldm,v) f
    Just a -> isTrue (oldm,v) (agtf a f) where AgT _ agtf = typeAtOf (oldm,v) a
  pss = map (fmap strip) oldpss
  strip set = filter ([]/=) $ map (filter (`elem` map fst ws)) set
\end{code}

Validity is truth at all worlds:
\begin{code}
isValid :: Model -> Form -> Bool
isValid m f = and [ isTrue (m,w) f | w <- map fst (fst m) ]
\end{code}

A toy example:
\begin{code}
myM :: Model
myM = ( [ (0,([0],[("Alice",liar)])),
          (1,([1],[("Alice",liar)])) ],
        [ ("Alice", [[0],[1]]) ] )
\end{code}

\begin{showCode}
*AGTYPES> canSay (myM,0) "Alice" (Prp 0)
False
*AGTYPES> canSay (myM,0) "Alice" (Prp 1)
True
*AGTYPES> canSay (myM,1) "Alice" (Prp 1)
False
*AGTYPES> canSay (myM,1) "Alice" (Prp 0)
True
\end{showCode}

\subsection{Example 3: Three inhabitants}

\begin{code}
example3m1, example3m2, example3m3, example3m4 :: Model
example3m1 =
  ( [ (1,([],[("A",liar),("B",liar),("C",liar)]))
    , (2,([],[("A",liar),("B",liar),("C",truthTeller)]))
    , (3,([],[("A",liar),("B",truthTeller),("C",truthTeller)]))
    , (4,([],[("A",liar),("B",truthTeller),("C",liar)]))
    , (5,([],[("A",truthTeller),("B",truthTeller),("C",truthTeller)]))
    , (6,([],[("A",truthTeller),("B",truthTeller),("C",liar)]))
    , (7,([],[("A",truthTeller),("B",liar),("C",liar)]))
    , (8,([],[("A",truthTeller),("B",liar),("C",truthTeller)]))
    ], [ ("D", [[1..8]]) ] )

example3m2 = announce example3m1 (Just "A") ("B" `IsA` liar)
example3m3 = announce example3m2 (Just "B") ("C" `IsA` liar)
example3m4 = announce example3m3 (Just "C") (Conj ["A" `IsA` liar, "B" `IsA` liar])
\end{code}

\begin{showCode}
*AGTYPES> example3m4
([(4,([],[("A",liar),("B",truthTeller),("C",liar)]))],[("D",[[4]])])
\end{showCode}

\subsection{Example 4: Death or Freedom}

\begin{code}
example4m1 :: Model
example4m1 =
  ( [ (1,([1],[("A",truthTeller),("B",liar)]))
    , (2,([1],[("A",liar),("B",truthTeller)]))
    , (3,([ ],[("A",truthTeller),("B",liar)]))
    , (4,([ ],[("A",liar),("B",truthTeller)]))
    ], [ ("C", [[1..4]]) ] )
\end{code}
``If I am a Knight, then the road behind me leads to Freedom,
and if I am a Knave, then the road behind me leads to Death.'':
\begin{code}
example4solution :: Form
example4solution = Conj
  [ impl ("A" `IsA` truthTeller) (Prp 1)
  , impl ("A" `IsA` liar) (Neg $ Prp 1) ]
\end{code}

\begin{showCode}
*AGTYPES> isTrue (example4m1,1) (diamAnnounce "A" example4solution $ K "C" (Prp 1))
True
\end{showCode}

% p. 132

\begin{code}
example4solutionAlt :: Form
example4solutionAlt =
  ("A" `IsA` truthTeller) `impl` Conj
    [ Prp 1         `impl` diamAnnounce "A" (diamAnnounce "B" (Neg $ Prp 1) Top) (kw "C" (Prp 1))
    , (Neg $ Prp 1) `impl` diamAnnounce "A" (diamAnnounce "B" (Neg $ Prp 1) Top) (kw "C" (Prp 1)) ]
\end{code}

\begin{showCode}
*AGTYPES> isTrue (example4m1,1) example4solutionAlt
True
\end{showCode}

Making the example harder:

\begin{code}
example4harderm1 :: Model
example4harderm1 =
  ( [ (1,([1],[("A",subjTruthTeller),("B",subjTruthTeller)]))
    , (2,([1],[("A",subjTruthTeller),("B",subjLiar)]))
    , (3,([ ],[("A",subjTruthTeller),("B",subjLiar)]))
    , (4,([ ],[("A",subjTruthTeller),("B",subjTruthTeller)]))
    , (5,([1],[("A",subjLiar),("B",subjTruthTeller)]))
    , (6,([1],[("A",subjLiar),("B",subjLiar)]))
    , (7,([ ],[("A",subjLiar),("B",subjLiar)]))
    , (8,([ ],[("A",subjLiar),("B",subjTruthTeller)]))
    ], [ ("A",[[1,2],[3,4],[5,6],[7,8]])
       , ("B",[[1,5],[2,6],[3,7],[4,8]])
       , ("C", [[1..8]]) ] )

example4harderValid :: Form
example4harderValid = Conj
  [ Neg $ kw "A" ("B" `IsA` subjTruthTeller)
  , K "C" $ Neg $ kw "A" ("B" `IsA` subjTruthTeller)
  , kw "A" (Prp 1)
  , Neg $ kw "C" (Prp 1)
  , Neg $ kw "C" ("A" `IsA` subjTruthTeller) ]
\end{code}

\begin{showCode}
*AGTYPES> isValid example4harderm1 example4harderValid
True
\end{showCode}

We can check that the previous solution and a subjective variant do not work any more:

\begin{code}
example4solutionAltSubj :: Form
example4solutionAltSubj =
  ("A" `IsA` subjTruthTeller) `impl` Conj
    [ Prp 1         `impl` diamAnnounce "A" (diamAnnounce "B" (Neg $ Prp 1) Top) (kw "C" (Prp 1))
    , (Neg $ Prp 1) `impl` diamAnnounce "A" (diamAnnounce "B" (Neg $ Prp 1) Top) (kw "C" (Prp 1)) ]
\end{code}

\begin{showCode}
*AGTYPES> isTrue (example4harderm1,2) (diamAnnounce "A" (diamAnnounce "B" (Neg $ (Prp 1)) Top) (kw "C" (Prp 1)))
False
*AGTYPES> isTrue (example4harderm1,2) example4solutionAltSubj
False
\end{showCode}

% p. 133

However, we can fix the short solution to ``I would say my path leads to Freedom (if I were asked)''.

\begin{code}
check1, check2, modSolution :: Form
check1 = diamAnnounce "A" (diamAnnounce "A" (Prp 1) Top) Top
check2 = diamAnnounce "A" (Prp 1) Top
modSolution =
  ("A" `IsA` subjTruthTeller) `impl` Conj
    [ Prp 1         `impl` diamAnnounce "A" (diamAnnounce "A" (Prp 1) Top) (kw "C" (Prp 1))
    , (Neg $ Prp 1) `impl` diamAnnounce "A" (diamAnnounce "A" (Neg $ Prp 1) Top) (kw "C" (Prp 1)) ]
\end{code}

\begin{showCode}
*AGTYPES> isTrue (example4harderm1,5) check1
True
*AGTYPES> isTrue (example4harderm1,5) check2
False
*AGTYPES> isValid example4harderm1 modSolution
True
\end{showCode}

\subsection{Translation to PALT}

We can translate PALTT to PALT as follows:
\begin{code}
delta :: [AgentType] -> AgentName -> Form -> Form
delta allT a phi =
  disj [ Conj [ a `IsA` eta, agTfct a phi ] | eta@(AgT _ agTfct) <- allT ]

paltt2palt :: [AgentType] -> Form -> Form
paltt2palt _    Top = Top
paltt2palt _    (Prp p) = Prp p
paltt2palt _    (a `IsA` eta) = a `IsA` eta
paltt2palt allT (Neg f) = Neg $ paltt2palt allT f
paltt2palt allT (Conj fs) = Conj $ map (paltt2palt allT) fs
paltt2palt allT (K ag f) = K ag (paltt2palt allT f)
paltt2palt allT (Announce a psi phi) =
  GodAnnounce (paltt2palt allT $ delta allT a psi) (paltt2palt allT phi)
paltt2palt allT (GodAnnounce psi phi) =
  GodAnnounce (paltt2palt allT psi) (paltt2palt allT phi)
\end{code}

% TODO: Does Proposition 5 generalize to all types that are free of epistemics / can be locally evaluated?
