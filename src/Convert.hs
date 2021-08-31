{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Convert where

import Data.Void (Void)
import Prettyprinter (Doc, Pretty (..), angles, comma, hsep, nest, parens, viaShow, vsep)

data Prim = Fst | Snd | Add | Mul
  deriving (Show)

instance Pretty Prim where
  pretty a = pretty (show a)

data Type
  = TFloat
  | TTuple Type Type
  | TArr Type Type
  | TUnit
  deriving (Show)

instance Pretty Type where
  pretty TFloat = pretty "Float"
  pretty (TTuple a b) = pretty (a, b)
  pretty (TArr a b) = pretty a <> pretty "->" <> pretty b
  pretty TUnit = pretty "Unit"

data Pattern b where
  IgnoreCase :: Pattern Void
  VarCase :: Pattern ()
  TupleCase :: Pattern a -> Pattern b -> Pattern (Either b a) -- Bind the right-hand side tighter

deriving instance Show (Pattern b)

showPattern :: Pattern b -> (Show b => r) -> r
showPattern IgnoreCase r = r
showPattern VarCase r = r
showPattern (TupleCase a b) r = showPattern a $ showPattern b r

data Exp v
  = Lam (Exp (Either () v))
  | forall b. LamCase (Pattern b) (Exp (Either b v))
  | Diff Type (Exp v)
  | Var v
  | App (Exp v) (Exp v)
  | Tuple (Exp v) (Exp v)
  | Unit
  | Const Float
  | Zero (Exp v)
  | Primitive Prim

instance Functor Exp where
  fmap f (Lam body) = Lam $ fmap (fmap f) body
  fmap f (LamCase p body) = LamCase p $ fmap (fmap f) body
  fmap f (Diff t expr) = Diff t (fmap f expr)
  fmap f (Var v) = Var (f v)
  fmap g (App f x) = App (fmap g f) (fmap g x)
  fmap f (Tuple a b) = Tuple (fmap f a) (fmap f b)
  fmap _ Unit = Unit
  fmap _ (Const x) = Const x
  fmap f (Zero x) = Zero (fmap f x)
  fmap _ (Primitive x) = Primitive x

-- TODO: precedence and parens
instance Show v => Show (Exp v) where
  show (Lam body) = "Lam " <> show body
  show (LamCase p body) = showPattern p $ "LamCase " <> show p <> " " <> show body
  show (Diff t body) = "Diff " <> show t <> " " <> show body
  show (Var v) = "Var " <> show v
  show (App f x) = "App " <> show f <> " " <> show x
  show (Tuple a b) = "Tuple " <> show a <> " " <> show b
  show Unit = "Unit"
  show (Const x) = "Const " <> show x
  show (Zero x) = "Zero " <> show x
  show (Primitive x) = "Primitive " <> show x

newtype V v = V v

data Precedence x = Precedence Int x

parens' :: Ord a => a -> a -> Doc ann -> Doc ann
parens' n d x = if d > n then parens x else x

instance Pretty (Pattern b) where
  pretty VarCase = pretty "x"
  pretty IgnoreCase = pretty "_"
  pretty (TupleCase a b) = pretty (a, b)

instance Show v => Pretty (Precedence (Exp v)) where
  pretty (Precedence d (Lam body)) =
    parens' 10 d $
      nest 2 $
        vsep
          [ pretty "λ",
            pretty (Precedence 0 body)
          ]
  pretty (Precedence d (Diff _ expr)) = pretty (Precedence d expr) -- hide the tangent type for now
  pretty (Precedence d (LamCase p body)) =
    parens' 10 d $
      showPattern p $
        nest 2 $ vsep [pretty "λ" <> pretty p, pretty (Precedence 0 body)]
  pretty (Precedence _ (Var v)) = viaShow v
  pretty (Precedence d (App f x)) = parens' 10 d $ hsep [pretty (Precedence 11 f), pretty (Precedence 11 x)]
  pretty (Precedence _ (Tuple f x)) = angles $ hsep [pretty (Precedence 0 f) <> comma, pretty $ Precedence 0 x]
  pretty (Precedence _ Unit) = pretty "Unit"
  pretty (Precedence _ (Const x)) = pretty x
  pretty (Precedence d (Zero x)) = parens' 10 d $ hsep [pretty "zero", pretty (Precedence 11 x)]
  pretty (Precedence _ (Primitive p)) = pretty p

instance Show v => Pretty (Exp v) where
  pretty x = pretty (Precedence 0 x)

{-
-}

data Value
  = Closure (Value -> Value)
  | Pair Value Value
  | Number Float
  | UnitValue
  | TypeValue Type

instance Show Value where
  show (Closure _) = "<<closure>>"
  show (Pair a b) = show (a, b)
  show (Number x) = show x
  show UnitValue = "Unit"
  show (TypeValue t) = show t

-- \(a,b) -> c
-- \() -> x
-- \x -> c
--

{-
>>> pretty (convert IgnoreCase (Primitive Mul) :: Exp Void)
λ
  (λ
    (λ
      <Fst Left (), λ
        (λ
          (λ
            <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
      (λ
        <Left (), λ
          Left ()>) (λ
        (λ(x, x)
          <Right (Left ()), λ
            (λ(x, (x, x))
              <<Left (Right ()), Left (Left (Right ()))>, Left (Left (Left ()))>) (Right (Left (Left ())) Left ())>) ((λ
          (λ
            (λ
              <Fst Left (), λ
                (λ
                  (λ
                    <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
              <Mul Left (), λ
                <Unit, <Mul <Snd Right (Left ()), Left ()>, Mul <Fst Right (Left ()), Left ()>>>>) (Fst Left ()))) ((λ
            <Snd Left (), λ
              <Unit, <zero (Fst Right (Left ())), Left ()>>>) Left ())) <Right (Left ()), Left ()>))) (Fst Left ()))) ((λ
    <Unit, λ
      <Unit, zero Right (Left ())>>) Left ())

>>> pretty (convert IgnoreCase (Primitive Add) :: Exp Void)
λ
  (λ
    (λ
      <Fst Left (), λ
        (λ
          (λ
            <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
      (λ
        <Left (), λ
          Left ()>) (λ
        (λ(x, x)
          <Right (Left ()), λ
            (λ(x, (x, x))
              <<Left (Right ()), Left (Left (Right ()))>, Left (Left (Left ()))>) (Right (Left (Left ())) Left ())>) ((λ
          (λ
            (λ
              <Fst Left (), λ
                (λ
                  (λ
                    <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
              <Add Left (), λ
                <Unit, <Left (), Left ()>>>) (Fst Left ()))) ((λ
            <Snd Left (), λ
              <Unit, <zero (Fst Right (Left ())), Left ()>>>) Left ())) <Right (Left ()), Left ()>))) (Fst Left ()))) ((λ
    <Unit, λ
      <Unit, zero Right (Left ())>>) Left ())

>>> pretty (convert IgnoreCase (Primitive Fst) :: Exp Void)
λ
  (λ
    (λ
      <Fst Left (), λ
        (λ
          (λ
            <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
      (λ
        <Left (), λ
          Left ()>) (λ
        (λ(x, x)
          <Right (Left ()), λ
            (λ(x, (x, x))
              <<Left (Right ()), Left (Left (Right ()))>, Left (Left (Left ()))>) (Right (Left (Left ())) Left ())>) ((λ
          (λ
            (λ
              <Fst Left (), λ
                (λ
                  (λ
                    <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
              <Fst Left (), λ
                <Unit, <Left (), zero (Snd Right (Left ()))>>>) (Fst Left ()))) ((λ
            <Snd Left (), λ
              <Unit, <zero (Fst Right (Left ())), Left ()>>>) Left ())) <Right (Left ()), Left ()>))) (Fst Left ()))) ((λ
    <Unit, λ
      <Unit, zero Right (Left ())>>) Left ())

>>> pretty (App (Lam (Var (Left ()))) (Const 3) :: Exp Void)
(λ
  Left ()) 3.0
-}

swapD :: Exp a
swapD = sequenceD dupD (parallelD sndD fstD)

data Arrow
  = Identity
  | Sequence Arrow Arrow
  | Parallel Arrow Arrow
  | Curry Arrow
  | Uncurry Arrow
  | DiffArrow Type Arrow
  | ConstArrow Float
  | UnitArrow
  | Duplicate
  | PrimArrow Prim
  deriving (Show)

instance Pretty (Precedence Arrow) where
  pretty (Precedence _ Identity) = pretty "id"
  pretty (Precedence d (Sequence f g)) = parens' 6 d $ hsep [pretty (Precedence 6 f), pretty ">>>", pretty (Precedence 6 g)]
  pretty (Precedence d (Parallel f g)) = parens' 7 d $ hsep [pretty (Precedence 7 f), pretty "⊗", pretty (Precedence 7 g)]
  pretty (Precedence d (Curry f)) = parens' 10 d $ hsep [pretty "curry", pretty (Precedence 11 f)]
  pretty (Precedence d (Uncurry f)) = parens' 10 d $ hsep [pretty "uncurry", pretty (Precedence 11 f)]
  pretty (Precedence d (DiffArrow _ arr)) = pretty (Precedence d arr)
  pretty (Precedence d (ConstArrow x)) = parens' 10 d $ hsep [pretty "const", pretty x]
  pretty (Precedence d UnitArrow) = parens' 10 d $ hsep [pretty "const", pretty ()]
  pretty (Precedence _ Duplicate) = pretty "dup"
  pretty (Precedence _ (PrimArrow p)) = viaShow p

instance Pretty Arrow where
  pretty x = pretty (Precedence 0 x)

{-
>>> pretty $ diffArrow' (PrimArrow Fst)
λ
  <Fst Left (), λ
    <Unit, <Left (), zero (Snd Right (Left ()))>>>

>>> pretty $ diffArrow' (PrimArrow Add)
λ
  <Add Left (), λ
    <Unit, <Left (), Left ()>>>

>>> pretty $ diffArrow' (PrimArrow Mul)
λ
  <Mul Left (), λ
    <Unit, <Mul <Snd Right (Left ()), Left ()>, Mul <Fst Right (Left ()), Left ()>>>>

>>> pretty $ diffArrow' Duplicate
λ
  <<Left (), Left ()>, λ
    <Unit, Add Left ()>>

>>> pretty $ diffArrow' UnitArrow
λ
  <Unit, λ
    <Unit, zero Right (Left ())>>

\a -> ((), \da -> ((), zero a))

>>> pretty $ diffArrow' (Curry Identity)
λ
  (λ
    <Left (), λ
      Left ()>) (λ
    (λ(x, x)
      <Right (Left ()), λ
        (λ(x, (x, x))
          <<Left (Right ()), Left (Left (Right ()))>, Left (Left (Left ()))>) (Right (Left (Left ())) Left ())>) ((λ
      <Left (), λ
        <Unit, Left ()>>) <Right (Left ()), Left ()>))

-}
diffArrow :: Arrow -> Exp Void
diffArrow Identity = idD
diffArrow (Sequence f g) = sequenceD (diffArrow f) (diffArrow g)
diffArrow (Parallel f g) = parallelD (diffArrow f) (diffArrow g)
diffArrow (Curry f) = curryD (diffArrow f)
diffArrow (Uncurry f) = uncurryD (diffArrow f)
diffArrow (DiffArrow t f) = Diff t (diffArrow f)
diffArrow Duplicate = dupD
diffArrow (ConstArrow x) = constD (Const x)
diffArrow UnitArrow = constD Unit
diffArrow (PrimArrow Fst) = fstD
diffArrow (PrimArrow Snd) = sndD
diffArrow (PrimArrow Add) = addD
diffArrow (PrimArrow Mul) = mulD

diffArrow' :: Arrow -> Exp Void
diffArrow' = diffArrow

fanOutArrow :: Arrow -> Arrow -> Arrow
fanOutArrow f g = Sequence Duplicate (Parallel f g)

{-
>>> pretty $ convertArrow IgnoreCase $ Primitive Add
const () >>> curry (Snd >>> Add)

>>> pretty $ convertArrow' $ Primitive Add
Add
-}
convertArrow :: Pattern b -> Exp b -> Arrow
convertArrow ctx (Lam body) = Curry $ convertArrow (TupleCase ctx VarCase) body
convertArrow ctx (LamCase p body) = Curry $ convertArrow (TupleCase ctx p) body
convertArrow ctx (Var i) = convertVar ctx i
convertArrow ctx (App f x) = (convertArrow ctx f `fanOutArrow` convertArrow ctx x) `Sequence` Uncurry Identity
convertArrow ctx (Tuple a b) = convertArrow ctx a `fanOutArrow` convertArrow ctx b
convertArrow ctx (Diff x expr) = DiffArrow x (convertArrow ctx expr) -- TODO: is it true that the tangent of the second order is the same as the first order?
convertArrow _ (Zero _) = error "Cannot differentiate Zero, we need to get the type of the expression but we're not evaluating here..."
convertArrow _ Unit = UnitArrow
convertArrow _ (Const x) = ConstArrow x
convertArrow _ (Primitive p) = Sequence UnitArrow (constFun (PrimArrow p))

-- constFun :: (b `k` c) -> (a `k` (b -> c))
constFun :: Arrow -> Arrow
constFun f = Curry (Sequence (PrimArrow Snd) f)

-- unitFun :: (b `k` c) -> (() `k` (b -> c))
unitFun :: Arrow -> Arrow
unitFun = constFun

convert :: Pattern b -> Exp b -> Exp Void
convert ctx = diffArrow . convertArrow ctx

optimizeArrow :: Arrow -> Arrow
optimizeArrow (Uncurry (Curry f)) = optimizeArrow f
optimizeArrow (Uncurry (Sequence UnitArrow (Curry (Sequence (PrimArrow Snd) f)))) = optimizeArrow (Sequence (PrimArrow Snd) f)
optimizeArrow (Uncurry f) = Uncurry (optimizeArrow f)
optimizeArrow (Curry (Uncurry f)) = optimizeArrow f
optimizeArrow (Curry f) = Curry $ optimizeArrow f
optimizeArrow (Sequence (Curry (Parallel f Identity)) (Uncurry Identity)) = f
optimizeArrow (Sequence Identity f) = optimizeArrow f
optimizeArrow (Sequence f Identity) = optimizeArrow f
-- dup >>> const () ⊗ f >>> Snd = f
optimizeArrow (Sequence Duplicate (Sequence (Parallel UnitArrow f) (PrimArrow Snd))) = optimizeArrow f
optimizeArrow (Sequence Duplicate (Sequence (Parallel UnitArrow f) (Sequence (PrimArrow Snd) g))) = optimizeArrow $ Sequence f g
optimizeArrow (Sequence Duplicate (Parallel (PrimArrow Fst) (PrimArrow Snd))) = Identity
optimizeArrow (Sequence (Parallel f g) (Parallel x y)) = Parallel (optimizeArrow $ Sequence f x) (optimizeArrow $ Sequence g y)
optimizeArrow (Sequence (Sequence f g) h) = optimizeArrow (Sequence f (optimizeArrow $ Sequence g h))
optimizeArrow (Sequence f g) = Sequence (optimizeArrow f) (optimizeArrow g)
optimizeArrow (Parallel Identity Identity) = Identity
optimizeArrow (Parallel f g) = Parallel (optimizeArrow f) (optimizeArrow g)
optimizeArrow Identity = Identity
optimizeArrow (DiffArrow t arr) = DiffArrow t (optimizeArrow arr)
optimizeArrow (ConstArrow x) = ConstArrow x
optimizeArrow UnitArrow = UnitArrow
optimizeArrow Duplicate = Duplicate
optimizeArrow (PrimArrow p) = PrimArrow p

convertArrow' :: Exp Void -> Arrow
convertArrow' expr = optimizeArrow $ Sequence f g
  where
    -- () -> (a -> b)
    arr = convertArrow IgnoreCase expr
    -- ((), a) -> b
    g = Uncurry arr
    -- a -> ((), a)
    f = UnitArrow `fanOutArrow` Identity

convert' :: Exp Void -> Exp Void
convert' = diffArrow . convertArrow'

callD :: (Value -> (Value, Value -> (Value, Value))) -> Value -> Value -> (Value, Value, Value)
callD f a db =
  let (b, f') = f a
      (dx, da) = f' db
   in (b, dx, da)

callD' :: Value -> (Value -> (Value, Value -> (Value, Value))) -> (Value, Value, Value)
callD' a f =
  let (b, f') = f a
      (dx, da) = f' (ones (tangent b))
   in (b, dx, da)

tangent :: Value -> Type
tangent (Number _) = TFloat
tangent (Pair (TypeValue t) (Closure _)) = t
tangent (Pair a b) = TTuple (tangent a) (tangent b)
tangent UnitValue = TUnit
tangent (Closure _) = error "No tangent for closure"
tangent (TypeValue t) = error $ "No tangent for type " <> show t

ones :: Type -> Value
ones TFloat = Number 1
ones (TTuple a b) = Pair (ones a) (ones b)
ones TUnit = UnitValue
ones (TArr _ _) = Closure $ \v -> ones (tangent v)

{-
>>> pretty $ convert' (Primitive Add)
λ
  (λ
    (λ
      <Fst Left (), λ
        (λ
          (λ
            <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
      (λ
        (λ
          <Fst Left (), λ
            (λ
              (λ
                <Fst Left (), <Snd Left (), Snd Right (Left ())>>) ((Snd Right (Right (Right (Left ())))) (Fst Left ()))) ((Snd Right (Left ())) Left ())>) ((Fst Left ()) (Snd Right (Left ())))) ((λ
        (λ
          (λ
            <Fst Left (), λ
              (λ
                (λ
                  <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
            (λ
              <Left (), λ
                Left ()>) (λ
              (λ(x, x)
                <Right (Left ()), λ
                  (λ(x, (x, x))
                    <<Left (Right ()), Left (Left (Right ()))>, Left (Left (Left ()))>) (Right (Left (Left ())) Left ())>) ((λ
                (λ
                  (λ
                    <Fst Left (), λ
                      (λ
                        (λ
                          <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
                    <Add Left (), λ
                      <Unit, <Left (), Left ()>>>) (Fst Left ()))) ((λ
                  <Snd Left (), λ
                    <Unit, <zero (Fst Right (Left ())), Left ()>>>) Left ())) <Right (Left ()), Left ()>))) (Fst Left ()))) ((λ
          <Unit, λ
            <Unit, zero Right (Left ())>>) Left ())) (Fst Left ()))) (Fst Left ()))) ((λ
    (λ
      (λ
        <Fst Left (), λ
          (λ
            (λ
              <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
        (λ
          <<Fst (Fst Left ()), Fst (Snd Left ())>, λ
            (λ
              <<Fst (Fst Left ()), Fst (Snd Left ())>, <Snd (Fst Left ()), Snd (Snd Left ())>>) <(Snd (Fst Right (Left ()))) (Fst Left ()), (Snd (Snd Right (Left ()))) (Snd Left ())>>) <(λ
          <Unit, λ
            <Unit, zero Right (Left ())>>) (Fst Left ()), (λ
          <Left (), λ
            <Unit, Left ()>>) (Snd Left ())>) (Fst Left ()))) ((λ
      <<Left (), Left ()>, λ
        <Unit, Add Left ()>>) Left ())) Left ())

>>> callD (evalD (convert' (Primitive Add))) (Pair (Number 2) (Number 4)) (Number 5)
((2.0,4.0),((Unit,(Unit,Unit)),(Unit,(Unit,Unit))),(5.0,5.0))

>>> pretty $ convertArrow IgnoreCase $ Const 2
const 2.0

>>> pretty $ convertArrow IgnoreCase $ (Lam (Const 2))
curry (const 2.0)

>>> pretty $ convertArrow' (Lam (Const 3))
dup >>> const () ⊗ id >>> uncurry (curry (const 3.0))

>>> callD (evalD (convert' (Lam (Const 2)))) (Number 4) (Number 5)
(4.0,((Unit,(Unit,Unit)),Unit),0.0)

>>> pretty $ convertArrow IgnoreCase (Tuple (Const 2) (Const 3))
dup >>> const 2.0 ⊗ const 3.0

>>> pretty $ convertArrow' (Lam $ App (Primitive Add) (Tuple (Const 2) (Const 3)))
dup >>> const () ⊗ id >>> uncurry (curry (dup >>> (const () >>> curry (Snd >>> Add)) ⊗ (dup >>> const 2.0 ⊗ const 3.0) >>> uncurry id))

>>> pretty $ convertArrow IgnoreCase (App (Primitive Add) (Tuple (Const 2) (Const 3)))
dup >>> (const () >>> curry (Snd >>> Add)) ⊗ (dup >>> const 2.0 ⊗ const 3.0) >>> uncurry id

>>> callD (evalD $ convert' (Primitive Add)) (Pair (Number 2) (Number 3)) (Number 3)
((2.0,3.0),((Unit,(Unit,Unit)),(Unit,(Unit,Unit))),(3.0,3.0))

-}
evalD :: Exp Void -> (Value -> (Value, Value -> (Value, Value)))
evalD expr = case eval EmptyContext expr of
  Pair (TypeValue _) (Closure f) -> \a ->
    case f a of
      Pair b (Closure f') ->
        ( b,
          \db ->
            case f' db of
              Pair dx da -> (dx, da)
              x -> error $ "Not a tangent: " <> show x
        )
      x -> error $ "Not a diff result: " <> show x
  x -> error $ "Not a diff function: " <> show x

data Context v where
  EmptyContext :: Context Void
  Bind :: Value -> Context ()
  BindPair :: Context a -> Context b -> Context (Either b a)

eval :: Show v => Context v -> Exp v -> Value
eval ctx (Lam e) = Closure $ \a -> eval (BindPair ctx (Bind a)) e
eval ctx (LamCase p e) = Closure $ \a ->
  showPattern p $
    let x = patternMatch a p
     in eval (BindPair ctx x) e
  where
    patternMatch :: Value -> Pattern b -> Context b
    patternMatch v VarCase = Bind v
    patternMatch _ IgnoreCase = EmptyContext
    patternMatch (Pair a b) (TupleCase x y) = BindPair (patternMatch a x) (patternMatch b y)
    patternMatch v (TupleCase _ _) = error $ "Pattern match failed on pair: " <> show v
eval ctx (Var i) = lookupVar ctx i
  where
    lookupVar :: Context x -> x -> Value
    lookupVar EmptyContext v = case v of
    lookupVar (Bind a) _ = a
    lookupVar (BindPair as _) (Right v) = lookupVar as v
    lookupVar (BindPair _ bs) (Left v) = lookupVar bs v
eval ctx (App f x) =
  case (eval ctx f, eval ctx x) of
    (Closure vf, v) -> vf v
    v -> error $ "Cannot call non-function " <> show v
eval ctx (Tuple a b) = Pair (eval ctx a) (eval ctx b)
eval _ Unit = UnitValue
eval _ (Const x) = Number x
eval _ (Primitive Fst) = Closure go
  where
    go (Pair a _) = a
    go v = error $ "Cannot get fst of non-pair " <> show v
eval _ (Primitive Snd) = Closure go
  where
    go (Pair _ b) = b
    go v = error $ "Cannot get snd of non-pair" <> show v
eval _ (Primitive Add) = Closure go
  where
    go (Pair (Number a) (Number b)) = Number $ a + b
    go (Pair UnitValue UnitValue) = UnitValue
    go (Pair (Pair a b) (Pair c d)) = Pair (go (Pair a c)) (go (Pair b d))
    go x = error $ "Cannot add " <> show x
eval _ (Primitive Mul) = Closure go
  where
    go (Pair (Number a) (Number b)) = Number $ a * b
    go (Pair UnitValue UnitValue) = UnitValue
    go (Pair (Pair a b) (Pair c d)) = Pair (go (Pair a c)) (go (Pair b d))
    go x = error $ "Cannot multiply " <> show x
eval ctx (Zero expr) = zeroTangent (tangent (eval ctx expr))
eval ctx (Diff t expr) = Pair (TypeValue t) (eval ctx expr)

zeroTangent :: Type -> Value
zeroTangent TFloat = Number 0
zeroTangent (TTuple a b) = Pair (zeroTangent a) (zeroTangent b)
zeroTangent TUnit = UnitValue
zeroTangent (TArr a b) = error $ "No tangent for function: " <> show (pretty a) <> " -> " <> show (pretty b)

-- Treat Context as a heterogeneous list built up from tuples
-- TODO: Optimize convertVar with a proj primitive
convertVar :: Pattern v -> v -> Arrow
convertVar IgnoreCase v = case v of
convertVar VarCase () = Identity
convertVar (TupleCase a _) (Right v) = Sequence (PrimArrow Fst) (convertVar a v)
convertVar (TupleCase _ b) (Left v) = Sequence (PrimArrow Snd) (convertVar b v)

-- (a -> a)
idD :: Exp a
idD = Diff TUnit $ Lam (Tuple (Var (Left ())) (Lam (Tuple Unit (Var (Left ())))))

{-
   idD = \a -> (a, \db -> ((), db))
-}

-- b -> (a -> b)
constD :: Exp a -> Exp a
constD b = Diff TUnit $ Lam body
  where
    {-
       constD b = \a -> (b, \db -> ((), zero a))
    -}
    pullback = Tuple Unit (Zero (Var (Right (Left ()))))
    body = Tuple (shift b) (Lam pullback)

let' :: Exp a -> Exp (Either () a) -> Exp a
let' x e = App (Lam e) x

shift :: Exp a -> Exp (Either () a)
shift = fmap Right

fst' :: Exp a -> Exp a
fst' = App (Primitive Fst)

snd' :: Exp a -> Exp a
snd' = App (Primitive Snd)

{-
>>> pretty $ convertArrow' $ Primitive Add
Add

>>> convertArrow' $ Primitive Add
PrimArrow Add

>>> callD' (Number 3) (evalD $ diffArrow' Duplicate)
((3.0,3.0),Unit,2.0)

>>> callD' (Pair (Number 2) (Number 3)) (evalD $ diffArrow' (PrimArrow Mul))
(6.0,Unit,(3.0,2.0))

>>> pretty $ diffArrow' Duplicate
λ
  <<Left (), Left ()>, λ
    <Unit, Add Left ()>>

>>> pretty $ diffArrow' (Sequence Identity Identity)
λ
  (λ
    (λ
      <Fst Left (), λ
        (λ
          (λ
            <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
      <Left (), λ
        <Unit, Left ()>>) (Fst Left ()))) ((λ
    <Left (), λ
      <Unit, Left ()>>) Left ())

>>> pretty $ diffArrow' Identity
λ
  <Left (), λ
    <Unit, Left ()>>
>>> pretty $ diffArrow' (Sequence Duplicate Identity)
λ
  (λ
    (λ
      <Fst Left (), λ
        (λ
          (λ
            <<Fst Left (), Fst Right (Left ())>, Snd Left ()>) ((Snd Right (Right (Right (Left ())))) (Snd Left ()))) ((Snd Right (Left ())) Left ())>) ((λ
      <Left (), λ
        <Unit, Left ()>>) (Fst Left ()))) ((λ
    <<Left (), Left ()>, λ
      <Unit, Add Left ()>>) Left ())

>>> callD' (Number 3) (evalD $ diffArrow' (Sequence Duplicate (Parallel Identity Identity)))
((3.0,3.0),(Unit,(Unit,Unit)),2.0)

>>> callD' (Number 3) (evalD $ diffArrow' (Sequence Duplicate (Parallel UnitArrow Identity)))
((Unit,3.0),(Unit,(Unit,Unit)),1.0)

-}
add' :: Exp a -> Exp a
add' = App (Primitive Add)

mul' :: Exp a -> Exp a
mul' = App (Primitive Mul)

id' :: Exp a
id' = Lam (Var (Left ()))

-- (a -> b) -> (b -> c) -> (a -> c)
sequenceD :: Exp a -> Exp a -> Exp a
sequenceD (Diff tx f) (Diff ty g) = Diff (TTuple tx ty) $ Lam body
  where
    {-
       sequenceD f g = \a ->
        let (b, f') = f a
            (c, g') = g b
        in (c, \dc ->
          let (y, db) = g' dc
              (x, da) = f' db
           in ((x,y), da)
          )
    -}
    -- b
    a = Var (Left ())
    b = fst' (Var (Left ()))
    body =
      let' (App (shift f) a) $
        let' (App (shift $ shift g) b) (Tuple c (Lam pullback))
    c = fst' (Var (Left ()))
    g' = snd' (Var (Right (Left ())))
    f' = snd' (Var (Right $ Right $ Right (Left ())))
    db = snd' (Var (Left ()))
    x = fst' (Var (Left ()))
    y = fst' (Var (Right (Left ())))
    da = snd' (Var (Left ()))
    pullback = let' (App g' (Var (Left ()))) $ let' (App f' db) (Tuple (Tuple x y) da)
sequenceD _ _ = error "Cannot sequence"

-- (a -> b) -> (a -> c) -> (a -> (b,c))
fanOut :: Exp a -> Exp a -> Exp a
fanOut f g = sequenceD dupD (parallelD f g)

dupD :: Exp a
dupD = Diff TUnit $ Lam (Tuple (Tuple a a) pullback)
  where
    {-
       dupD = \a -> ((a,a), \(da,db) -> ((), add (da,db)))
    -}
    a = Var (Left ())
    p = Var (Left ())
    pullback = Lam (Tuple Unit (add' p))

parallelD :: Exp a -> Exp a -> Exp a
parallelD (Diff tx f) (Diff ty g) = Diff (TTuple tx ty) $ Lam body
  where
    {-
       parallelD f g = \(a,c) ->
        let ((b, f'), (d,g')) = (f a, g c)
        in ((b,d) \(db, dd) ->
          let ((x,da), (y, dc)) = (f' db, g' dd)
          in ((x,y), (da,dc))
        )
    -}
    a = fst' (Var (Left ()))
    c = snd' (Var (Left ()))
    b = fst' $ fst' (Var (Left ()))
    d = fst' $ snd' (Var (Left ()))
    body =
      let' (Tuple (App (shift f) a) (App (shift g) c)) $
        Tuple (Tuple b d) (Lam pullback)
    f' = snd' $ fst' $ Var $ Right (Left ())
    g' = snd' $ snd' $ Var $ Right (Left ())
    db = fst' (Var (Left ()))
    dd = snd' (Var (Left ()))
    x = fst' $ fst' (Var (Left ()))
    da = snd' $ fst' (Var (Left ()))
    y = fst' $ snd' (Var (Left ()))
    dc = snd' $ snd' (Var (Left ()))
    pullback =
      let' (Tuple (App f' db) (App g' dd)) $
        Tuple (Tuple x y) (Tuple da dc)
parallelD _ _ = error "Cannot parallel"

-- (a -> b, a) -> b
applyD :: Exp a
applyD = Diff TUnit $ Lam body
  where
    {-
       applyD = \(f,a) ->
        let (b,f') = f a
        in (b, \db -> ((), f' db))
    -}
    f = fst' (Var (Left ()))
    a = snd' (Var (Left ()))
    b = fst' (Var (Left ()))
    body = let' (App f a) (Tuple b (Lam pullback))
    f' = snd' $ Var (Right (Left ()))
    db = Var (Left ())
    pullback = Tuple Unit (App f' db)

letCase :: Pattern b -> Exp v -> Exp (Either b v) -> Exp v
letCase p x body = App (LamCase p body) x

reassoc :: Exp (Either (Either () ()) ())
reassoc =
  let x = Var (Right ())
      da = Var (Left (Right ()))
      db = Var (Left (Left ()))
   in Tuple (Tuple x da) db

-- ((a,b) -> c) -> (a -> (b -> c))
-- (dc -> (dx, (da, db))) (a,b) -> c : Tan c = dc
-- (dc -> ((dx, da), db) b -> c : Tan (b -> c) = (dx, da)
-- ((dx, da) -> (dx, da)) (a -> (b -> c))
curryD :: Show a => Exp a -> Exp a
curryD (Diff tx f) =
  Diff tx $
    Lam $
      let g =
            Lam $
              let a = Var (Right (Left ()))
                  b = Var (Left ())
               in letCase (TupleCase VarCase VarCase) (App (shift $ shift f) (Tuple a b)) $
                    let c = Var (Right (Left ()))
                     in Tuple c $
                          Lam $
                            let dc = Var $ Left ()
                                f' = Var $ Right (Left $ Left ())
                             in letCase (TupleCase VarCase (TupleCase VarCase VarCase)) (App f' dc) $ fmap Left reassoc
       in let' g (Tuple (Var (Left ())) id')
{-
curryD (Diff tx f) = Diff tx $ Lam body
  where
    {-
       curryD f = \a ->
        let g = \b ->
          let (c, f') = f (a,b)
           in (c, \dc ->
              let (x, (da, db)) = f' dc
              in ((x, da), db)
            )
        in (g, \r -> r)

        λa (λg (g, λr r))
            (λb
              (λpc
                ( Fst pc
                , λdc
                  (λdfs
                    ( (Fst dfs {x}, Fst (Snd dfs) {da}) , Snd (Snd dfs) {db} )
                  )
                  ((Snd pc {f'}) dc) )
              )
              (f ( a , b ))
            )
    -}
    a = Var (Right (Left ()))
    b = Var (Left ())
    c = fst' (Var (Left ()))
    f' = snd' (Var (Right (Left ())))
    dc = Var (Left ())
    x = fst' (Var (Left ()))
    da = fst' $ snd' (Var (Left ()))
    db = snd' $ snd' (Var (Left ()))
    pullback = let' (App f' dc) (Tuple (Tuple x da) db)
    g = let' (App (shift $ shift f) (Tuple a b)) (Tuple c (Lam pullback))
    body = let' (Lam g) (Tuple (Var (Left ())) id')
-}
curryD expr = error $ "No curry for: " <> show expr

uncurryD :: Exp a -> Exp a
uncurryD (Diff tx f) = Diff tx $ Lam body
  where
    {-
       uncurryD f = \(a,b) ->
        let (g, f') = f a
            (c, g') = g b
        in (c, \dc ->
          let (y, db) = g' dc
              (x, da) = f' y
          in (x, (da, db))
        )
    -}
    body =
      let' (App (shift f) (fst' (Var (Left ())))) $
        let' (App (fst' (Var (Left ()))) (snd' (Var (Right (Left ()))))) $
          Tuple (fst' (Var (Left ()))) (Lam pullback)
    g' = snd' $ Var $ Right $ Left ()
    dc = Var $ Left ()
    f' = snd' $ Var $ Right $ Right $ Right $ Left ()
    y = fst' $ Var (Left ())
    x = fst' $ Var (Left ())
    da = snd' $ Var (Left ())
    db = snd' $ Var (Right $ Left ())
    pullback =
      let' (App g' dc) $
        let' (App f' y) $
          Tuple x (Tuple da db)
uncurryD _ = error "uncurry: Not a diff function"

fstD :: Exp a
fstD = Diff TUnit $ Lam body
  where
    {-
       fstD = \(a,b) -> (a, \da -> ((), (da, zero b)))
    -}
    b = snd' (Var (Right (Left ())))
    pullback = Tuple Unit (Tuple (Var (Left ())) (Zero b))
    a = fst' (Var (Left ()))
    body = Tuple a (Lam pullback)

sndD :: Exp a
sndD = Diff TUnit $ Lam body
  where
    {-
       sndD = \(a,b) -> (b, \db -> ((), (zero a, db)))
    -}
    a = fst' (Var (Right (Left ())))
    pullback = Tuple Unit (Tuple (Zero a) (Var (Left ())))
    b = snd' (Var (Left ()))
    body = Tuple b (Lam pullback)

addD :: Exp a
addD = Diff TUnit $ Lam body
  where
    {-
       addD = \(a,b) -> (a + b, \dc -> ((), (dc, dc)))
    -}
    pullback = Tuple Unit (Tuple (Var (Left ())) (Var (Left ())))
    body = Tuple (add' (Var (Left ()))) (Lam pullback)

mulD :: Exp a
mulD = Diff TUnit $ Lam body
  where
    {-
       mulD = \(a,b) -> (a * b, \dc -> ((), (b * dc, a * dc)))
    -}
    dc = Var (Left ())
    a = fst' (Var (Right (Left ())))
    b = snd' (Var (Right (Left ())))
    pullback = Tuple Unit (Tuple (mul' (Tuple b dc)) (mul' (Tuple a dc)))
    body = Tuple (mul' (Var (Left ()))) (Lam pullback)
