{-# LANGUAGE ViewPatterns #-}    
{-# LANGUAGE TypeOperators #-}

type Var = String

data Lambda = Var :=> Exp
    deriving (Show,Eq,Ord)

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp
    deriving (Show,Eq,Ord)
		
terminal :: (a -> a) -> (a -> Bool) -> a -> a
terminal f isFinal ς0 | isFinal ς0 = ς0
                      | otherwise  = terminal f isFinal (f(ς0))

collect :: (a -> a) -> (a -> Bool) -> a -> [a]
collect f isFinal ς0 | isFinal ς0 = [ς0]
                     | otherwise  = ς0 : (collect f isFinal (f(ς0)))

infixr 9 ==>
infixr 9 // 

(==>) :: a -> b -> (a,b)
(==>) x y = (x,y)

(//) :: Eq a => (a -> b) -> [(a,b)] -> (a -> b)
(//) f [(x,y)] = \ x' -> if (x == x') then y else f(x')
					
type Σ = (Exp, Env, Cont)

data D = Clo(Lambda, Env)

type Env = Var -> D

data Cont = Mt | Ar (Exp, Env, Cont) | Fn (Lambda, Env, Cont)

inject :: Exp -> Σ
inject (e) = (e, ρ0, Mt)
 where ρ0 :: Env
       ρ0 = \ x -> error $ "no binding for " ++ x

isFinal :: Σ -> Bool
isFinal (Lam _, ρ, Mt) = True
isFinal _              = False

step :: Σ -> Σ
step (Ref x, ρ, κ)                    = (Lam lam, ρ', κ) where Clo(lam, ρ') = ρ(x)
step (f :@ e, ρ, κ)                   = (f, ρ,  Ar(e, ρ, κ))
step (Lam lam, ρ, Ar(e, ρ', κ))       = (e, ρ', Fn(lam, ρ, κ))
step (Lam lam, ρ, Fn(x :=> e, ρ', κ)) = (e, ρ' // [x ==> Clo(lam, ρ)], κ)

evaluate :: Exp -> Exp
evaluate e = case terminal step isFinal (inject(e)) of 
	(e', _, _) -> e'

-- (((lambda (x) x) (lambda (z) z)) (lambda (a) a))

main :: IO ()
main = do 
	print (evaluate $! ((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")))
	return ()


-- evaluate (((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))) :@ (Lam ("a" :=> Ref "a")), ρ0, Mt)

-- (((Lam ("x" :=> Ref "x")) :@ (Lam ("z" :=> Ref "z"))), ρ0, Ar((Lam ("a" :=> Ref "a")), ρ0, Mt))

-- ((Lam ("x" :=> Ref "x")), ρ0, Ar((Lam ("z" :=> Ref "z")), ρ0, Ar((Lam ("a" :=> Ref "a")), ρ0, Mt)))

-- ((Lam ("z" :=> Ref "z")), ρ0, Fn(("x" :=> Ref "x"), ρ0, Ar((Lam ("a" :=> Ref "a")), ρ0, Mt)))

-- (Ref "x", ρ0 // ["x" ==> Clo(("z" :=> Ref "z"), ρ0)], Ar((Lam ("a" :=> Ref "a")), ρ0, Mt))

-- ((Lam ("z" :=> Ref "z")), ρ0, Ar((Lam ("a" :=> Ref "a")), ρ0, Mt))

-- ((Lam ("a" :=> Ref "a")), ρ0, Fn(("z" :=> Ref "z"), ρ0, Mt))

-- (("z" :=> Ref "z"), ρ0 // ["z" :=> Clo(("a" :=> Ref "a"), ρ0)], Mt)

-- ((Lam ("a" :=> Ref "a")), ρ0, Mt)

-- (Lam ("a" :=> Ref "a"))