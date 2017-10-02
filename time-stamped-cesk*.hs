-- The time-stamped CESK* Machine

{-# LANGUAGE ViewPatterns #-}    
{-# LANGUAGE TypeOperators #-}

import Data.Map hiding (foldl)

---------------  syntax  --------------

type Var = String

data Lambda = Var :=> Exp
    deriving (Show,Eq,Ord)

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp
    deriving (Show,Eq,Ord)

---------------  reachability  --------------

terminal :: (a -> a) -> (a -> Bool) -> a -> a
terminal f isFinal ς0 | isFinal ς0 = ς0
                      | otherwise  = terminal f isFinal (f(ς0))

collect :: (a -> a) -> (a -> Bool) -> a -> [a]
collect f isFinal ς0 | isFinal ς0 = [ς0]
                     | otherwise  = ς0 : (collect f isFinal (f(ς0)))

---------------  auxiliary functions  --------------

type k :-> v = Map k v

(==>) :: a -> b -> (a,b)
(==>) x y = (x,y)

(//) :: Ord a => (a :-> b) -> [(a,b)] -> (a :-> b)
(//) f [(x,y)] = Data.Map.insert x y f

-----------------------------

type Σ = (Exp,Env,Store,Kont,Time)

data Storable = Clo (Lambda, Env) | Cont Kont

type Env = Var :-> Addr

type Store = Addr :-> Storable

data Kont = Mt | Ar (Exp,Env,Addr) | Fn (Lambda,Env,Addr)

type Addr = Int

type Time = Int

inject :: Exp -> Σ
inject (e) = (e, ρ0, σ0, κ0, t0)
    where ρ0 = Data.Map.empty
          σ0 = Data.Map.empty 
          κ0 = Mt
          t0 = 0

isFinal :: Σ -> Bool
isFinal (Lam _, _, σ, Mt, _) = True
isFinal _ = False

evaluate :: Exp -> Exp
evaluate e = case terminal step isFinal (inject(e)) of 
    (e', _, _, _, _) -> e'

step :: Σ -> Σ
step ς@(Ref x, ρ, σ, κ, t) = (Lam lam, ρ', σ, κ, t')  
    where 
        Clo(lam, ρ') = σ!(ρ!x)
        t' = tick(ς)

step ς@(f :@ e, ρ, σ, κ, t) = (f, ρ, σ', κ', t')
    where
        a' = alloc(ς)
        σ' = σ // [a' ==> Cont κ]
        κ' = Ar(e, ρ, a')
        t' = tick(ς)

step ς@(Lam lam, ρ, σ, Ar(e, ρ', a'), t) = (e, ρ', σ, Fn(lam, ρ, a'), t') 
    where
        t' = tick(ς)

step ς@(Lam lam, ρ, σ, Fn(x :=> e, ρ', a), t) = (e, ρ' // [x ==> a'], σ // [a' ==> Clo(lam, ρ)], κ, t')
    where
        Cont κ = σ!a
        a' = alloc(ς)
        t' = tick(ς)

alloc :: Σ -> Addr
alloc (_,_,σ,_,_) = (foldl max 0 $! keys σ) + 1

tick :: Σ -> Time
tick (_,_,_,_,t) = t + 1

-----------------------------

main :: IO ()
main = do
    print (evaluate $! ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")))
    return ()

--	((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a"))

--	(((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")),
--	                                                      fromList [],
--	                                                      fromList [],
--	                                                      Mt,
--	                                                      0)

--	((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z")),
--	                                                    fromList [],
--	                                                    fromList [(1, Cont(Mt))],
--	                                                    Ar((Lam ("a" :=> Ref "a"))), fromList [], 1),
--	                                                    1)

--	((Lam ("x" :=> Ref "x")),
--	                        fromList [],
--	                        fromList [(1, Cont(Mt)), (2, Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1))))],
--	                        Ar((Lam ("z" :=> Ref "z")), fromList [], 2),
--	                        2)

--	((Lam ("z" :=> Ref "z")),
--	                        fromList [],
--	                        fromList [(1, Cont(Mt)), (2, Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1))))],
--	                        Fn(("x" :=> Ref "x"), fromList [], 2),
--	                        3)

--	(Ref "x",
--	     fromList [("x", 3)],
--	     fromList [(1, Cont(Mt)), (2, Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1)), (3, Clo(("z" :=> Ref "z"), fromList []))],
--	     Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1),
--	     4)

--	((Lam ("z" :=> Ref "z")),
--	                        fromList [],
--	                        fromList [(1, Cont(Mt)), (2, Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1)), (3, Clo(("z" :=> Ref "z"), fromList []))],
--	                        Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1),,
--	                        5)

--	((Lam ("a" :=> Ref "a")),
--	                        fromList [],
--	                        fromList [(1, Cont(Mt)), (2, Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1)), (3, Clo(("z" :=> Ref "z"), fromList []))],
--	                        Fn(("z" :=> Ref "z"), fromList [], 1),
--	                        6)

--	(Ref "z",
--	     fromList [("z", 4)],
--	     fromList [(1, Cont(Mt)), (2, Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1)), (3, Clo(("z" :=> Ref "z"), fromList [])), (4, Clo(("a" :=> Ref "a"), fromList []))],
--	     Cont(Mt),
--	     7)

--	((Lam ("a" :=> Ref "a")),
--	      fromList [],
--	      fromList [(1, Cont(Mt)), (2, Cont(Ar((Lam ("a" :=> Ref "a"))), fromList [], 1)), (3, Clo(("z" :=> Ref "z"), fromList [])), (4, Clo(("a" :=> Ref "a"), fromList []))],
--	      Cont(Mt),
--	      8)