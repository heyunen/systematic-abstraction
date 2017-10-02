-- The CESK* Machine

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

type Σ = (Exp,Env,Store,Addr)

data Kont = Mt | Ar (Exp,Env,Addr) | Fn (Lambda,Env,Addr)
    deriving Show

data Storable = Clo (Lambda, Env) | Cont Kont
    deriving Show

type Env = Var :-> Addr

type Store = Addr :-> Storable

type Addr = Int

isAr :: Storable -> Bool
isAr (Cont (Ar _)) = True
isAr (_) = False

isFn :: Storable -> Bool
isFn (Cont(Fn _)) = True
isFn (_) = False

isMt :: Storable -> Bool
isMt (Cont(Mt)) = True
isMt (_) = False

inject :: Exp -> Σ
inject (e) = (e, ρ0, σ0, ahalt)
  where ρ0 = Data.Map.empty
        σ0 = Data.Map.empty // [ahalt ==> Cont(Mt)]
        ahalt = 0

isFinal :: Σ -> Bool
isFinal (Lam _, _, σ, a) = isMt(σ!a)
isFinal _ = False

evaluate :: Exp -> Exp
evaluate e = case terminal step isFinal (inject(e)) of
    (e', _, _, _) -> e'

step :: Σ -> Σ
step (Ref x, ρ, σ, a) = (Lam lam, ρ', σ, a)  
    where 
        Clo(lam, ρ') = σ!(ρ!x)

step (f :@ e, ρ, σ, a) = (f, ρ, σ', a')
    where
        a' = alloc(σ)
        σ' = σ // [a' ==> Cont(Ar(e, ρ, a))]

step (Lam lam, ρ, σ, a) | isAr(σ!a) = (e, ρ', σ', a'') 
    where 
        Cont(Ar(e, ρ', a')) = σ!a
        a'' = alloc(σ)
        σ' = σ // [a'' ==> Cont(Fn(lam, ρ, a'))]

step (Lam lam, ρ, σ, a) | isFn(σ!a) = (e, ρ' // [x ==> a'], σ // [a' ==> Clo(lam, ρ)], a'') 
    where 
        Cont(Fn(x :=> e, ρ', a'')) = σ!a
        a' = alloc(σ)

alloc :: Store -> Addr
alloc(σ) = (foldl max 0 $! keys σ) + 1

-----------------------------

main :: IO ()
main = do
    print (evaluate $! ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")))
    return ()

-- ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a"))

-- (((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")), fromList [], fromList [(0, Cont(Mt))], 0)

-- ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z")), fromList [], fromList [(0, Cont(Mt)),
--                                                                            (1, Cont(Ar((Lam ("a" :=> Ref "a")), fromList [], 0)))], 1)

-- ((Lam ("x" :=> Ref "x")), fromList [], fromList [(0, Cont(Mt)),
--	                                                (1, Cont(Ar((Lam ("a" :=> Ref "a")), fromList [], 0))),
--	                                                (2, Cont(Ar((Lam ("z" :=> Ref "z")), fromList [], 1)))], 2)

-- ((Lam ("z" :=> Ref "z")), fromList [], fromList [(0, Cont(Mt)),
--	                                                (1, Cont(Ar((Lam ("a" :=> Ref "a")), fromList [], 0))),
--	                                                (2, Cont(Ar((Lam ("z" :=> Ref "z")), fromList [], 1)))
--	                                                (3, Cont(Fn(("x" :=> Ref "x"), fromList [], 1)))], 3)

-- (Ref "x", fromList [("x", 4)], fromList [(0, Cont(Mt)),
--	                                        (1, Cont(Ar((Lam ("a" :=> Ref "a")), fromList [], 0))),
--	                                        (2, Cont(Ar((Lam ("z" :=> Ref "z")), fromList [], 1)))
--	                                        (3, Cont(Fn(("x" :=> Ref "x"), fromList [], 1)))
--	                                        (4, Clo(("z" :=> Ref "z"), fromList []))], 1)

-- ((Lam ("z" :=> Ref "z")), fromList [], fromList [(0, Cont(Mt)),
--	                                                (1, Cont(Ar((Lam ("a" :=> Ref "a")), fromList [], 0))),
--	                                                (2, Cont(Ar((Lam ("z" :=> Ref "z")), fromList [], 1)))
--	                                                (3, Cont(Fn(("x" :=> Ref "x"), fromList [], 1)))
--	                                                (4, Clo(("z" :=> Ref "z"), fromList []))], 1)

-- ((Lam ("a" :=> Ref "a")), fromList [], fromList [(0, Cont(Mt)),
--	                                                (1, Cont(Ar((Lam ("a" :=> Ref "a")), fromList [], 0))),
--	                                                (2, Cont(Ar((Lam ("z" :=> Ref "z")), fromList [], 1)))
--	                                                (3, Cont(Fn(("x" :=> Ref "x"), fromList [], 1)))
--	                                                (4, Clo(("z" :=> Ref "z"), fromList []))
--	                                                (5, Cont(Fn(("a" :=> Ref "a"), fromList [], 0)))])

-- (Lam ("a" :=> Ref "a"))