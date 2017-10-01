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

type Σ = (Exp,Env,Store,Kont)

type Env = Var :-> Addr

data Storable = Clo (Lambda, Env)
    deriving Show

type Store = Addr :-> Storable

data Kont = Mt | Ar(Exp,Env,Kont) | Fn(Lambda,Env,Kont)

type Addr = Int

inject :: Exp -> Σ 
inject (e) = (e, ρ0, σ0, Mt) 
    where 
      ρ0 = Data.Map.empty
      σ0 = Data.Map.empty

isFinal :: Σ -> Bool
isFinal (Lam _, _, _, Mt) = True
isFinal _                 = False

evaluate :: Exp -> Exp
evaluate e = case terminal step isFinal (inject(e)) of 
    (e', _, _, _) -> e'

step :: Σ -> Σ 
step (Ref x, ρ, σ, κ) = (Lam lam, ρ', σ, κ)
    where Clo(lam, ρ') = σ!(ρ!x)
step (f :@ e, ρ, σ, κ) = (f, ρ, σ, Ar(e, ρ, κ))
step (Lam lam, ρ, σ, Ar(e, ρ', κ)) = (e, ρ', σ, Fn(lam, ρ, κ))
step (Lam lam, ρ, σ, Fn(x :=> e, ρ', κ)) = (e, ρ' // [x ==> a'], σ // [a' ==> Clo(lam, ρ)], κ) 
    where a' = alloc(σ)


alloc :: Store -> Addr
alloc(σ) = (foldl max 0 $! keys σ) + 1

-----------------------------

main :: IO ()
main = do
    print (evaluate $! ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")))
    return ()

-- ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a"))

-- ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")), ρ0, σ0, Mt)

-- ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")), fromList [], fromList [], Mt)

-- ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z")), fromList [], fromList [], Ar((Lam ("a" :=> Ref "a")), fromList [], Mt))

-- ((Lam ("x" :=> Ref "x")), fromList [], fromList [], Ar((Lam ("z" :=> Ref "z")), fromList [], Ar((Lam ("a" :=> Ref "a")), fromList [], Mt)))

-- ((Lam ("z" :=> Ref "z")), fromList [], fromList [], Fn(("x" :=> Ref "x"), fromList [], Ar((Lam ("a" :=> Ref "a")), fromList [], Mt)))

-- (("x" :=> Ref "x"), fromList [("x", 1)], fromList [(1, Clo("z" :=> Ref "z", fromList []))], Ar((Lam ("a" :=> Ref "a")), fromList [], Mt))

-- ((Lam ("z" :=> Ref "z")), fromList [], fromList [(1, Clo("z" :=> Ref "z", fromList []))], Ar((Lam ("a" :=> Ref "a")), fromList [("x",1)], Mt))

-- ((Lam ("a" :=> Ref "a")), fromList [], fromList [(1, Clo("z" :=> Ref "z", fromList []))], Fn("z" :=> Ref "z", fromList [], Ar((Lam ("a" :=> Ref "a")), fromList [("x", 1)], Mt)))

-- (Ref "z", fromList [("z", 2)], fromList [(1, Clo("z" :=> Ref "z", fromList [])), (2, Clo("a" :=> Ref "a", fromList []))], Ar((Lam ("a" :=> Ref "a")), fromList [("x", 1)], Mt))

-- ((Lam ("a" :=> Ref "a")), fromList [], fromList [(1, Clo("z" :=> Ref "z", fromList [])), (2, Clo("a" :=> Ref "a", fromList []))], Ar((Lam ("a" :=> Ref "a")), fromList [("x", 1)], Mt))

-- ((Lam ("a" :=> Ref "a")), fromList [("x",1)], fromList [(1, Clo("z" :=> Ref "z", fromList [])), (2, Clo("a" :=> Ref "a", fromList []))], Fn("a" :=> Ref "a", fromList [], Mt))

-- (Ref "a", fromList [("x", 1), ("a", 2)], fromList [(1, Clo("z" :=> Ref "z", fromList [])), (2, Clo("a" :=> Ref "a", fromList [])), (3, Clo("a" :=> Ref "a", fromList []))], Mt)

-- (Lam ("a" :=> Ref "a"), fromList [], fromList [(1, Clo("z" :=> Ref "z", fromList [])), (2, Clo("a" :=> Ref "a", fromList [])), (3, Clo("a" :=> Ref "a", fromList []))], Mt)

-- Lam ("a" :=> Ref "a")