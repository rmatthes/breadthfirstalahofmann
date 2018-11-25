import Control.Monad.State

-- For usage see Section 6.

-- Implementing functions of the breadthfirst paper in Haskell

-- 1. Definition of bf-traversal (breadthfirstspec) acting as a specification
-- 2. Martin Hofmann's definition of bf-traversal (breadthfirst, S_MH)
-- 3. Predicative algorithm using Rou' (breadthfirst', S_pred1)
-- 4. Predicative algorithm using Rou'' (breadthfirst'', S_pred2)
-- 5. Display and creation of trees
-- 6. Experiments


-- 1. Definition of bf-traversal (breadthfirstspec) acting as a specification
-- ==========================================================================

type Nat = Int

data Tree = Leaf Nat | Node Tree Nat Tree

flatten :: [[a]] -> [a]
flatten = concat

zip' :: [[a]] -> [[a]] -> [[a]]
zip' [] ll = ll
zip' ll [] = ll
zip' (l:ll) (l':ll') = (l ++ l') : zip' ll ll'

niveaux :: Tree -> [[Nat]]
niveaux (Leaf n) = [[n]]
niveaux (Node t1 n t2) = [n] : (zip' (niveaux t1) (niveaux t2))

breadthfirstspec :: Tree -> [Nat]
breadthfirstspec t = flatten (niveaux t)


-- 2. Martin Hofmann's definition of bf-traversal (breadthfirst, S_MH)
-- ===================================================================

data Rou = Over | Next ((Rou -> [Nat]) -> [Nat])

unfold :: Rou -> (Rou -> [Nat]) -> [Nat] 
unfold Over     k = k Over
unfold (Next f) k = f k

br :: Tree -> Rou -> Rou
br (Leaf n) c = 
     Next (\ k-> n : unfold c k)
br (Node t1 n t2) c = 
     Next (\ k-> n : unfold c (k . br t1 . br t2))

extract :: Rou -> [Nat]
extract Over = []
extract (Next f) = f extract

breadthfirst :: Tree -> [Nat]
breadthfirst t = extract (br t Over)

  
-- 3. Predicative algorithm using Rou' (breadthfirst', S_pred1)
-- ============================================================

type Rou' = [[Nat] -> [Nat]]

cons :: a -> [a] -> [a]
cons = (:)

br' :: Tree -> Rou' -> Rou'
br' (Leaf n) [] = [cons n]
br' (Leaf n) (g : gs) = (cons n . g) : gs
br' (Node tl n tr) [] = cons n : br' tl (br' tr [])
br' (Node tl n tr) (g : gs) = (cons n . g) : br' tl (br' tr gs)

extract' :: Rou' -> [Nat]
extract' [] = []
extract' (g : gs) = g (extract' gs)

breadthfirst' :: Tree -> [Nat]
breadthfirst' t = extract' (br' t []) 


-- 4. Predicative algorithm using Rou'' (breadthfirst'', S_pred2)
-- ==============================================================

type Rou'' = [[Nat]]

br'' :: Tree -> Rou'' -> Rou''
br'' (Leaf n) [] = [[n]]
br'' (Leaf n) (l : ls) = (n : l) : ls
br'' (Node tl n tr) [] = [n] : br'' tl (br'' tr [])
br'' (Node tl n tr) (l : ls) = (n : l) : br'' tl (br'' tr ls)

breadthfirst'' :: Tree -> [Nat]
breadthfirst'' t = flatten (br'' t []) 


-- 5. Display and creation of trees
-- =================================

showsTree :: Tree -> [String]
showsTree (Leaf n) = [show n]
showsTree (Node t1 n t2) =
        map (" . "++) (showsTree t1)
     ++ [show n]
     ++ map (" . " ++) (showsTree t2)

showTree :: Tree -> String
showTree = concat . map ("\n" ++) . showsTree

pT :: Tree -> IO ()
pT = putStrLn . showTree

-- make tree labelled in depth-first order
makeTree :: Nat -> State Nat Tree
makeTree depth =
  if depth == 0
  then do { n <- get ; put (n+1) ; return (Leaf n) }
  else do { 
            n <- get ; 
            put (n+1) ;
            t1 <- makeTree (depth-1) ; 
            t2 <- makeTree (depth-1) ; 
            return (Node t1 n t2)
          }

-- make tree of given depth with 0 as root label            
mT :: Nat -> Tree
mT depth = evalState (makeTree depth) 0

-- make tree of given depth labelled by depth of node
mTd :: Nat -> Tree
mTd depth = aux 0
  where
    aux n = if n >= depth 
            then Leaf n 
            else let {t = aux (n+1)}
                 in Node t n t

-- make infinite tree labelled by depth of node + given n
mTi :: Int -> Tree
mTi n = let {t = mTi (n+1)}
        in Node t n t


-- 6. Experiments
-- ==============

{-
*Main> pT (mT 3)

 .  .  . 3
 .  . 2
 .  .  . 4
 . 1
 .  .  . 6
 .  . 5
 .  .  . 7
0
 .  .  . 10
 .  . 9
 .  .  . 11
 . 8
 .  .  . 13
 .  . 12
 .  .  . 14
*Main> :set +s
*Main> sum (breadthfirstspec (mT 20))
2199020109825
(12.01 secs, 4,884,212,056 bytes)
*Main> sum (breadthfirst (mT 20))
2199020109825
(11.16 secs, 3,793,442,784 bytes)
*Main> sum (breadthfirst' (mT 20))
2199020109825
(10.46 secs, 3,752,773,264 bytes)
*Main> sum (breadthfirst'' (mT 20))
2199020109825
(9.62 secs, 3,569,096,952 bytes)
*Main> take 10 (breadthfirstspec (mTi 0))
[0,1,1,2,2,2,2,3,3,3]
(0.01 secs, 0 bytes)
*Main> take 10 (breadthfirst (mTi 0))
[0,1,1,2,2,2,2,3,3,3]
(0.01 secs, 0 bytes)
*Main> take 10 (breadthfirst' (mTi 0))
[0,1,1,2,2,2,2,3,3,3]
(0.01 secs, 0 bytes)
*Main> take 10 (breadthfirst'' (mTi 0))
[0,1,1,2,2,2,2,3,3,3]
(0.01 secs, 0 bytes)
*Main> 
-}

