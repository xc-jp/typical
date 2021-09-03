{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Convert where

import Data.Void (Void, absurd)
import Prettyprinter (Doc, Pretty (..), angles, comma, hsep, nest, parens, sep, viaShow)

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
  TupleCase :: Pattern a -> Pattern b -> Pattern (Either a b) -- Bind the right-hand side tighter

deriving instance Show (Pattern b)

showPattern :: Pattern b -> (Show b => r) -> r
showPattern IgnoreCase r = r
showPattern VarCase r = r
showPattern (TupleCase a b) r = showPattern a $ showPattern b r

data Exp' ann v
  = Lam ann (Exp' ann (Either v ()))
  | forall b. LamCase (Pattern b) ann (Exp' ann (Either v b))
  | Diff (Exp' ann v) (Exp' ann v) -- the first expression should evaluate to a type
  | Var v
  | App (Exp' ann v) (Exp' ann v)
  | Tuple (Exp' ann v) (Exp' ann v)
  | Unit
  | Const Float
  | Zero (Exp' ann v)
  | Primitive Prim
  | Type Type
  | Tangent (Exp' ann v)

type Exp = Exp' ()

instance Functor (Exp' ann) where
  fmap f (Lam ann body) = Lam ann $ fmap (mapLeft f) body
  fmap f (LamCase p ann body) = LamCase p ann $ fmap (mapLeft f) body
  fmap f (Diff t expr) = Diff (fmap f t) (fmap f expr)
  fmap f (Var v) = Var (f v)
  fmap g (App f x) = App (fmap g f) (fmap g x)
  fmap f (Tuple a b) = Tuple (fmap f a) (fmap f b)
  fmap _ Unit = Unit
  fmap _ (Const x) = Const x
  fmap f (Zero x) = Zero (fmap f x)
  fmap _ (Primitive x) = Primitive x
  fmap _ (Type t) = Type t
  fmap f (Tangent x) = Tangent (fmap f x)

mapLeft :: (a -> b) -> Either a x -> Either b x
mapLeft f (Left a) = Left (f a)
mapLeft _ (Right x) = Right x

-- TODO: precedence and parens
instance (Show v, Show ann) => Show (Exp' ann v) where
  showsPrec d (Lam ann body) =
    showParen (d > 10) $
      showString "Lam "
        . showsPrec 11 ann
        . showString " "
        . showsPrec 11 body
  showsPrec d (LamCase p ann body) =
    showPattern p $
      showParen (d > 10) $
        showString "LamCase "
          . showsPrec 11 p
          . showString " "
          . showsPrec 11 ann
          . showString " "
          . showsPrec 11 body
  showsPrec d (Diff t body) =
    showParen (d > 10) $
      showString "Diff "
        . showsPrec 11 t
        . showString " "
        . showsPrec 11 body
  showsPrec d (Var v) =
    showParen (d > 10) $
      showString "Var "
        . showsPrec 11 v
  showsPrec d (App f x) =
    showParen (d > 10) $
      showString "App "
        . showsPrec 11 f
        . showString " "
        . showsPrec 11 x
  showsPrec d (Tuple a b) =
    showParen (d > 10) $
      showString "Tuple "
        . showsPrec 11 a
        . showString " "
        . showsPrec 11 b
  showsPrec _ Unit = showString "Unit"
  showsPrec d (Const x) =
    showParen (d > 10) $
      showString "Const "
        . showsPrec 11 x
  showsPrec d (Zero x) =
    showParen (d > 10) $
      showString "Zero "
        . showsPrec 11 x
  showsPrec d (Primitive x) =
    showParen (d > 10) $
      showString "Primitive "
        . showsPrec 11 x
  showsPrec d (Type t) =
    showParen (d > 10) $
      showString "Type "
        . showsPrec 11 t
  showsPrec d (Tangent expr) =
    showParen (d > 10) $
      showString "Tangent "
        . showsPrec 11 expr

newtype V v = V v

data Precedence x = Precedence Int x

parens' :: Ord a => a -> a -> Doc ann -> Doc ann
parens' n d x = if d > n then parens x else x

instance Pretty (V Void) where
  pretty (V x) = pretty x

instance Pretty (V String) where
  pretty (V x) = pretty x

instance Pretty (V ()) where
  pretty (V x) = pretty x

instance (Pretty (V v), Pretty (V b)) => Pretty (V (Either v b)) where
  pretty (V (Right _)) = pretty "()"
  pretty (V (Left x)) = pretty (V x)

instance Pretty (Pattern b) where
  pretty VarCase = pretty "x"
  pretty IgnoreCase = pretty "_"
  pretty (TupleCase a b) = pretty (a, b)

prettyPattern :: Pattern b -> (Pretty (V b) => r) -> r
prettyPattern IgnoreCase r = r
prettyPattern VarCase r = r
prettyPattern (TupleCase a b) r = prettyPattern a $ prettyPattern b r

instance (Pretty (V v)) => Pretty (Precedence (Exp' String v)) where
  pretty (Precedence d (Lam ann body)) =
    parens' 10 d $
      nest 2 $
        sep
          [ pretty ("λ" <> ann <> "."),
            pretty (Precedence 0 body)
          ]
  pretty (Precedence d (Diff t expr)) = parens' 10 d $ sep [pretty "Diff " <> pretty (Precedence 0 t), pretty (Precedence d expr)]
  pretty (Precedence d (LamCase p ann body)) =
    parens' 10 d $
      prettyPattern p $
        nest 2 $ sep [pretty ("λ" <> ann <> "."), pretty (Precedence 0 body)]
  pretty (Precedence _ (Var v)) = pretty (V v)
  pretty (Precedence d (App f x)) = parens' 10 d $ sep [pretty (Precedence 11 f), pretty (Precedence 11 x)]
  pretty (Precedence _ (Tuple f x)) = angles $ sep [pretty (Precedence 0 f) <> comma, pretty $ Precedence 0 x]
  pretty (Precedence _ Unit) = pretty "Unit"
  pretty (Precedence _ (Const x)) = pretty x
  pretty (Precedence d (Zero x)) = parens' 10 d $ sep [pretty "zero", pretty (Precedence 11 x)]
  pretty (Precedence _ (Primitive p)) = pretty p
  pretty (Precedence _ (Type p)) = pretty p
  pretty (Precedence d (Tangent x)) = parens' 10 d $ sep [pretty "tangent", pretty (Precedence 11 x)]

instance Pretty (Exp Void) where
  pretty x = pretty (Precedence 0 (named x))

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

{-
>> pretty (convert IgnoreCase (Primitive Mul) :: Exp Void)

>>> pretty (App (Lam () $ Lam () (Var (Right ()))) (Const 3) :: Exp Void)
(λx0. λx1. x1) 3.0
-}

swapD :: Exp a
swapD = sequenceD dupD (parallelD sndD fstD)

data Arrow
  = Identity
  | Sequence Arrow Arrow
  | Parallel Arrow Arrow
  | Curry Arrow
  | Uncurry Arrow
  | ConstArrow Float
  | UnitArrow
  | Duplicate
  | PrimArrow Prim
  | ZeroArrow
  | TypeArrow Type
  | TangentArrow
  deriving (Show)

instance Pretty (Precedence Arrow) where
  pretty (Precedence _ Identity) = pretty "id"
  pretty (Precedence d (Sequence f g)) = parens' 6 d $ hsep [pretty (Precedence 7 f), pretty ">>>", pretty (Precedence 6 g)]
  pretty (Precedence d (Parallel f g)) = parens' 7 d $ sep [pretty (Precedence 8 f), pretty "⊗", pretty (Precedence 7 g)]
  pretty (Precedence d (Curry f)) = parens' 10 d $ sep [pretty "curry", pretty (Precedence 11 f)]
  pretty (Precedence d (Uncurry f)) = parens' 10 d $ sep [pretty "uncurry", pretty (Precedence 11 f)]
  pretty (Precedence d (ConstArrow x)) = parens' 10 d $ sep [pretty "const", pretty x]
  pretty (Precedence d UnitArrow) = parens' 10 d $ sep [pretty "const", pretty ()]
  pretty (Precedence d (TypeArrow t)) = parens' 10 d $ sep [pretty "type", pretty t]
  pretty (Precedence _ TangentArrow) = pretty "tangent"
  pretty (Precedence _ ZeroArrow) = pretty "zero"
  pretty (Precedence _ Duplicate) = pretty "dup"
  pretty (Precedence _ (PrimArrow p)) = viaShow p

instance Pretty Arrow where
  pretty x = pretty (Precedence 0 x)

{-
>>> pretty $ diffArrow' (PrimArrow Fst)
Diff Unit λx0. <Fst x0, λx1. <Unit, <x1, zero (Snd x0)>>>

>>> pretty $ diffArrow' (PrimArrow Add)
Diff Unit λx0. <Add x0, λx1. <Unit, <x1, x1>>>

>>> pretty $ diffArrow' (PrimArrow Mul)
Diff Unit λx0. <Mul x0, λx1. <Unit, <Mul <Snd x0, x1>, Mul <Fst x0, x1>>>>

>>> pretty $ diffArrow' Duplicate
Diff Unit λx0. <<x0, x0>, λx1. <Unit, Add x1>>

>>> pretty $ diffArrow' UnitArrow
Diff Unit λx0. <Unit, λx1. <Unit, zero x0>>

>>> pretty $ diffArrow' Duplicate
Diff Unit λx0. <<x0, x0>, λx1. <Unit, Add x1>>

>>> pretty $ diffArrow' (ConstArrow 2)
Diff Unit λx0. <2.0, λx1. <Unit, zero x0>>

>>> pretty $ diffArrow' TangentArrow
Diff Unit λx0. <tangent x0, λx1. <Unit, zero x0>>

>>> pretty $ diffArrow' (Curry Identity)
Diff Unit
λx0.
  (λx1. <x1, λx2. x2>)
  (Diff <Unit, tangent x0>
  (λx1.
    (λx2.
      <Fst x2,
      λx3. (λx4. <<Fst x4, Fst (Snd x4)>, Snd (Snd x4)>) ((Snd x2) x3)>)
    ((λx2. <x2, λx3. <Unit, x3>>) <x0, x1>)))
-}
diffArrow :: Arrow -> Exp Void
diffArrow Identity = idD
diffArrow (Sequence f g) = sequenceD (diffArrow f) (diffArrow g)
diffArrow (Parallel f g) = parallelD (diffArrow f) (diffArrow g)
diffArrow (Curry f) = curryD (diffArrow f)
diffArrow (Uncurry f) = uncurryD (diffArrow f)
diffArrow Duplicate = dupD
diffArrow (ConstArrow x) = constD (Const x)
diffArrow UnitArrow = constD Unit
diffArrow (PrimArrow Fst) = fstD
diffArrow (PrimArrow Snd) = sndD
diffArrow (PrimArrow Add) = addD
diffArrow (PrimArrow Mul) = mulD
diffArrow TangentArrow = tangentD
diffArrow (TypeArrow t) = constD (Type t)
diffArrow ZeroArrow = zeroD

diffArrow' :: Arrow -> Exp Void
diffArrow' = diffArrow

fanOutArrow :: Arrow -> Arrow -> Arrow
fanOutArrow f g = Sequence Duplicate (Parallel f g)

{-
>>> pretty $ convertArrow IgnoreCase $ Primitive Add
const () >>> curry (Snd >>> Add)

>>> pretty $ convertArrow' $ Primitive Add
Add

>>> pretty $ convertArrow' $ Lam () $ Lam () $ (Var (Right ()))
dup >>> const () ⊗ id >>> curry Snd

>>> pretty $ convertArrow' $ Lam () $ Lam () $ (Var (Left (Right ())))
dup >>> const () ⊗ id >>> curry (Fst >>> Snd)

>>> pretty $ convertArrow' $ Lam () $ Lam () $ Zero (Var (Left (Right ())))
dup >>> const () ⊗ id >>> curry (Fst >>> Snd >>> zero)

>>> pretty (LamCase (TupleCase VarCase VarCase) () (Zero (Var (Right (Left ())))) :: Exp Void)
λ(x0,x1). zero x0

>>> pretty (Lam () $ LamCase (TupleCase (TupleCase VarCase VarCase) VarCase) () (Zero (Var (Right (Right ())))) :: Exp Void)
λx0. λ((x1,x2),x3). zero x3

-}
convertArrow :: Pattern b -> Exp b -> Arrow
convertArrow ctx (Lam _ body) = Curry $ convertArrow (TupleCase ctx VarCase) body
convertArrow ctx (LamCase p _ body) = Curry $ convertArrow (TupleCase ctx p) body
convertArrow ctx (Var i) = convertVar ctx i
convertArrow ctx (App f x) = (convertArrow ctx f `fanOutArrow` convertArrow ctx x) `Sequence` Uncurry Identity
convertArrow ctx (Tuple a b) = convertArrow ctx a `fanOutArrow` convertArrow ctx b
convertArrow ctx (Diff _ expr) = convertArrow ctx expr
convertArrow ctx (Zero expr) = Sequence (convertArrow ctx expr) ZeroArrow
convertArrow ctx (Tangent expr) = Sequence (convertArrow ctx expr) TangentArrow
convertArrow _ Unit = UnitArrow
convertArrow _ (Const x) = ConstArrow x
convertArrow _ (Type t) = TypeArrow t
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
optimizeArrow (ConstArrow x) = ConstArrow x
optimizeArrow UnitArrow = UnitArrow
optimizeArrow Duplicate = Duplicate
optimizeArrow (PrimArrow p) = PrimArrow p
optimizeArrow ZeroArrow = ZeroArrow
optimizeArrow (TypeArrow t) = TypeArrow t
optimizeArrow TangentArrow = TangentArrow

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

callD :: Value -> Value -> Value -> (Value, Value, Value)
callD g a db =
  let f = diffValue g
      (b, f') = f a
      (dx, da) = f' db
   in (b, dx, da)

callD' :: Value -> Value -> (Value, Value, Value)
callD' a g =
  let f = diffValue g
      (b, f') = f a
      (dx, da) = f' (ones (tangent b))
   in (b, dx, da)

-- >>> tangent (eval EmptyContext (Diff (Tuple (Type TUnit) (Tangent (Const 2))) (Lam (Var (Left ())))))
-- TTuple TUnit TFloat
tangent :: Value -> Type
tangent (Number _) = TFloat
tangent (Pair (TypeValue t) (Closure _)) = t
tangent (Pair a b) = TTuple (tangent a) (tangent b)
tangent UnitValue = TUnit
tangent (TypeValue _) = TUnit
tangent (Closure _) = error "No tangent for closure"

ones :: Type -> Value
ones TFloat = Number 1
ones (TTuple a b) = Pair (ones a) (ones b)
ones TUnit = UnitValue
ones (TArr _ _) = Closure $ \v -> ones (tangent v)

{-
>>> pretty $ convert' (Primitive Add)
Diff Unit λx0. <Add x0, λx1. <Unit, <x1, x1>>>

>>> callD (evalD (convert' (Primitive Add))) (Pair (Number 2) (Number 4)) (Number 5)
(6.0,TUnit,(5.0,5.0))

>>> pretty $ convertArrow IgnoreCase $ Const 2
const 2.0

>>> pretty $ convertArrow IgnoreCase $ (Lam () (Const 2))
curry (const 2.0)

>>> pretty $ convertArrow' (Lam () (Const 3))
dup >>> const () ⊗ id >>> const 3.0

>>> callD (evalD (convert' (Lam () (Const 2)))) (Number 4) (Number 5)
(2.0,(Unit,((Unit,Unit),Unit)),0.0)

>>> pretty $ convertArrow IgnoreCase (Tuple (Const 2) (Const 3))
dup >>> const 2.0 ⊗ const 3.0

>>> pretty $ convertArrow' (Lam () $ App (Primitive Add) (Tuple (Const 2) (Const 3)))
dup >>> const () ⊗ id >>> dup >>> (const () >>> curry (Snd >>> Add))
⊗
(dup >>> const 2.0 ⊗ const 3.0) >>> uncurry id

>>> pretty $ convertArrow' (App (Primitive Add) (Tuple (Const 2) (Const 3)))
dup >>> const () ⊗ id >>> uncurry
(dup >>> (const () >>> curry (Snd >>> Add))
⊗
(dup >>> const 2.0 ⊗ const 3.0) >>> uncurry id)

>>> callD (evalD $ convert' (Primitive Add)) (Pair (Number 2) (Number 3)) (Number 3)
(5.0,TUnit,(3.0,3.0))

-}

diffValue :: Value -> (Value -> (Value, Value -> (Value, Value)))
diffValue (Pair (TypeValue _) (Closure f)) a =
  case f a of
    Pair b (Closure f') ->
      ( b,
        \db ->
          case f' db of
            Pair dx da -> (dx, da)
            x -> error $ "Not a tangent: " <> show x
      )
    x -> error $ "Not a diff result: " <> show x
diffValue x _ = error $ "Not a diff function: " <> show x

evalD :: Exp Void -> Value
evalD = eval EmptyContext

data Context v where
  EmptyContext :: Context Void
  Bind :: Value -> Context ()
  BindPair :: Context a -> Context b -> Context (Either a b)

eval :: Show v => Context v -> Exp v -> Value
eval ctx (Lam _ e) = Closure $ \a -> eval (BindPair ctx (Bind a)) e
eval ctx (LamCase p _ e) = Closure $ \a ->
  showPattern p $
    let x = patternMatch a p
     in eval (BindPair ctx x) e
  where
    patternMatch :: Value -> Pattern b -> Context b
    patternMatch v VarCase = Bind v
    patternMatch _ IgnoreCase = EmptyContext
    patternMatch (Pair a b) (TupleCase ctxa ctxb) = BindPair (patternMatch a ctxa) (patternMatch b ctxb)
    patternMatch v (TupleCase _ _) = error $ "Pattern match failed on pair: " <> show v
eval ctx (Var i) = lookupVar ctx i
  where
    lookupVar :: Context x -> x -> Value
    lookupVar EmptyContext v = case v of
    lookupVar (Bind a) _ = a
    lookupVar (BindPair as _) (Left v) = lookupVar as v
    lookupVar (BindPair _ bs) (Right v) = lookupVar bs v
eval ctx (App f x) =
  case (eval ctx f, eval ctx x) of
    (Closure vf, v) -> vf v
    -- we need to be able to call differentiable functions, maybe they should have a special form as values instead of
    -- being a pair with the type representation
    (Pair (TypeValue _) (Closure vf), v) -> vf v
    v -> error $ "Cannot call non-function " <> show v
eval ctx (Tuple a b) = Pair (eval ctx a) (eval ctx b)
eval _ (Type t) = TypeValue t
eval ctx (Tangent expr) = TypeValue $ tangent (eval ctx expr)
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
eval ctx (Diff tag expr) = Pair (TypeValue $ toType (eval ctx tag)) (eval ctx expr)
  where
    toType (Pair a b) = TTuple (toType a) (toType b)
    toType (TypeValue t) = t
    toType v = error $ show v <> " is not a type"

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
convertVar (TupleCase a _) (Left v) = Sequence (PrimArrow Fst) (convertVar a v)
convertVar (TupleCase _ b) (Right v) = Sequence (PrimArrow Snd) (convertVar b v)

-- (a -> a)
idD :: Exp a
idD = Diff (Type TUnit) $ Lam () (Tuple (Var (Right ())) (Lam () (Tuple Unit (Var (Right ())))))

{-
   idD = \a -> (a, \db -> ((), db))
-}

-- b -> (a -> b)
constD :: Exp a -> Exp a
constD b = Diff (Type TUnit) $ Lam () body
  where
    {-
       constD b = \a -> (b, \db -> ((), zero a))
    -}
    pullback = Tuple Unit (Zero (Var (Left (Right ()))))
    body = Tuple (shift b) (Lam () pullback)

-- zeroD a ~= constD (zero a) (it takes a from the input right now)
zeroD :: Exp Void
zeroD = Diff (Type TUnit) $ Lam () body
  where
    {-
     zeroD = \a -> (zero a :: da, \dda -> ((), zero a :: da))
    -}
    pullback = Tuple Unit (Zero (Var (Left (Right ()))))
    body = Tuple (Zero (Var (Right ()))) (Lam () pullback)

tangentD :: Exp Void
tangentD = Diff (Type TUnit) $ Lam () body
  where
    {-
     tangentD = \a -> (tangent a, \() -> ((), zero a))
    -}
    pullback = Tuple Unit (Zero (Var (Left (Right ()))))
    body = Tuple (Tangent (Var (Right ()))) (Lam () pullback)

let' :: Exp a -> Exp (Either a ()) -> Exp a
let' x e = App (Lam () e) x

shift :: Exp a -> Exp (Either a ())
shift = fmap Left

fst' :: Exp a -> Exp a
fst' = App (Primitive Fst)

snd' :: Exp a -> Exp a
snd' = App (Primitive Snd)

{-
>>> pretty $ diffArrow' $ convertArrow' (Lam () $ Lam () (Var (Right ())))
Diff <<Unit, <Unit, Unit>>, <Unit, Unit>>
λx0.
  (λx1.
    (λx2.
      <Fst x2,
      λx3.
        (λx4.
          (λx5. <<Fst x5, Fst x4>, Snd x5>) ((Snd x1) (Snd x4)))
        ((Snd x2) x3)>)
    ((λx2.
      (λx3.
        (λx4.
          <Fst x4,
          λx5.
            (λx6.
              (λx7. <Fst x7, <Snd x7, Snd x6>>) ((Snd x3) (Fst x6)))
            ((Snd x4) x5)>)
        ((Fst x3) (Snd x2)))
      ((λx3.
        (λx4.
          <x4, λx5. x5>)
        (Diff <<Unit, Unit>, tangent x3>
        (λx4.
          (λx5.
            <Fst x5,
            λx6.
              (λx7. <<Fst x7, Fst (Snd x7)>, Snd (Snd x7)>) ((Snd x5) x6)>)
          ((λx5.
            (λx6.
              <x6, λx7. x7>)
            (Diff <<Unit, Unit>, tangent x5>
            (λx6.
              (λx7.
                <Fst x7,
                λx8.
                  (λx9. <<Fst x9, Fst (Snd x9)>, Snd (Snd x9)>) ((Snd x7) x8)>)
              ((λx7.
                (λx8.
                  (λx9.
                    <Fst x9,
                    λx10.
                      (λx11.
                        (λx12.
                          <<Fst x12, Fst x11>, Snd x12>)
                        ((Snd x8) (Snd x11)))
                      ((Snd x9) x10)>)
                  ((λx9. <x9, λx10. <Unit, x10>>) (Fst x8)))
                ((λx8. <Snd x8, λx9. <Unit, <zero (Fst x8), x9>>>) x7))
              <x5, x6>))))
          <x3, x4>))))
      (Fst x2)))
    (Fst x1)))
  ((λx1.
    (λx2.
      (λx3.
        <Fst x3,
        λx4.
          (λx5.
            (λx6. <<Fst x6, Fst x5>, Snd x6>) ((Snd x2) (Snd x5)))
          ((Snd x3) x4)>)
      ((λx3.
        (λx4.
          <<Fst (Fst x4), Fst (Snd x4)>,
          λx5.
            (λx6.
              <<Fst (Fst x6), Fst (Snd x6)>, <Snd (Fst x6), Snd (Snd x6)>>)
            <(Snd (Fst x4)) (Fst x5), (Snd (Snd x4)) (Snd x5)>>)
        <(λx4. <Unit, λx5. <Unit, zero x4>>) (Fst x3),
        (λx4. <x4, λx5. <Unit, x5>>) (Snd x3)>)
      (Fst x2)))
    ((λx2. <<x2, x2>, λx3. <Unit, Add x3>>) x1))
  x0)
-}

{-
>>> pretty $ convertArrow' $ Primitive Add
Add

>>> convertArrow' $ Primitive Add
PrimArrow Add

>>> callD' (Number 3) (evalD $ diffArrow' Duplicate)
((3.0,3.0),Unit,2.0)

>>> callD' (Pair (Number 2) (Number 3)) (evalD $ diffArrow' (PrimArrow Mul))
(6.0,TUnit,(3.0,2.0))

>>> pretty $ diffArrow' Duplicate
Diff Unit λx0. <<x0, x0>, λx1. <Unit, Add x1>>

>>> pretty $ diffArrow' (Sequence Identity Identity)
Diff <Unit, Unit>
λx0.
  (λx1.
    (λx2.
      <Fst x2,
      λx3.
        (λx4. (λx5. <<Fst x5, Fst x4>, Snd x5>) ((Snd x1) (Snd x4)))
        ((Snd x2) x3)>)
    ((λx2. <x2, λx3. <Unit, x3>>) (Fst x1)))
  ((λx1. <x1, λx2. <Unit, x2>>) x0)

>>> pretty $ diffArrow' Identity
Diff Unit λx0. <x0, λx1. <Unit, x1>>
>>> pretty $ diffArrow' (Sequence Duplicate Identity)
Diff <Unit, Unit>
λx0.
  (λx1.
    (λx2.
      <Fst x2,
      λx3.
        (λx4. (λx5. <<Fst x5, Fst x4>, Snd x5>) ((Snd x1) (Snd x4)))
        ((Snd x2) x3)>)
    ((λx2. <x2, λx3. <Unit, x3>>) (Fst x1)))
  ((λx1. <<x1, x1>, λx2. <Unit, Add x2>>) x0)

>>> callD' (Number 3) (evalD $ diffArrow' (Sequence Duplicate (Parallel Identity Identity)))
((3.0,3.0),(Unit,(Unit,Unit)),2.0)

>>> callD' (Number 3) (evalD $ diffArrow' (Sequence Duplicate (Parallel UnitArrow Identity)))
((Unit,3.0),(Unit,(Unit,Unit)),1.0)

>>> callD' (Pair (Number 2) (Number 4)) $ fst3 $ callD' (Number 3) (evalD $ diffArrow' (Curry Identity))
((3.0,(2.0,4.0)),(Unit,1.0),(1.0,1.0))

>>> callD' (Number 3) (evalD $ diffArrow' $ convertArrow' $ Lam () (Zero (Var (Right ()))))
(0.0,Unit,0.0)

>>> pretty $ diffArrow' (Uncurry Identity)
Diff Unit
λx0.
  (λx1.
    (λx2.
      <Fst x2,
      λx3.
        (λx4. (λx5. <Fst x5, <Snd x5, Snd x4>>) ((Snd x1) (Fst x4)))
        ((Snd x2) x3)>)
    ((Fst x1) (Snd x0)))
  ((λx1. <x1, λx2. <Unit, x2>>) (Fst x0))

>>> pretty $ diffArrow' (Curry Identity)
Diff Unit
λx0.
  (λx1. <x1, λx2. x2>)
  (Diff <Unit, tangent x0>
  (λx1.
    (λx2.
      <Fst x2,
      λx3. (λx4. <<Fst x4, Fst (Snd x4)>, Snd (Snd x4)>) ((Snd x2) x3)>)
    ((λx2. <x2, λx3. <Unit, x3>>) <x0, x1>)))

>>> callD' (Pair (Number 3) (Number 4)) $ fst3 $ callD' UnitValue (evalD (diffArrow' (Curry Identity)))
((Unit,(3.0,4.0)),(Unit,Unit),(1.0,1.0))

>>> convertArrow' (Lam () $ Lam () (Var (Left (Right ()))))
Sequence Duplicate (Sequence (Parallel UnitArrow Identity) (Curry (Sequence (PrimArrow Fst) (PrimArrow Snd))))

>>> pretty $ convertArrow' (Lam () $ Lam () (Var (Left (Right ()))))
dup >>> const () ⊗ id >>> curry (Fst >>> Snd)

>>> evalD $ diffArrow' $ convertArrow' (Lam () $ Lam () (Var (Right ())))
(TTuple TUnit (TTuple (TTuple TUnit TUnit) TUnit),<<closure>>)

>>> pretty $ convertArrow' (Lam () $ Lam () (Var (Right ())))
dup >>> const () ⊗ id >>> curry Snd

>>> callD' (Number 2) $ evalD $ diffArrow' $ convertArrow' (Lam () $ Lam () (Var (Right ())))
((TTuple TUnit (TTuple TUnit TFloat),<<closure>>),(Unit,((Unit,Unit),Unit)),1.0)

>>> pretty $ convertArrow' (Lam () $ Lam () (Var (Right ())))
dup >>> const () ⊗ id >>> curry Snd

>>> pretty $ convertArrow' (Lam () $ Lam () (Var (Right ())))
dup >>> const () ⊗ id >>> curry Snd

>>> pretty (Lam () $ Lam () (Var (Right ())) :: Exp Void)
λx0. λx1. x1

>>> callD' (Number 6) $  fst3 $ callD' (Number 2) (evalD $ diffArrow' $ convertArrow' (Lam () $ Lam () (Var (Right ()))))
(6.0,(Unit,(Unit,0.0)),1.0)

>>> pretty (Lam () $ Lam () (Var (Left (Right ()))) :: Exp Void)
λx0. λx1. x0

>>> callD' (Number 6) $ fst3 $ callD' (Number 2) $ evalD $ diffArrow' $ convertArrow' (Lam () $ Lam () (Var (Left (Right ()))))
(2.0,((Unit,Unit),(Unit,1.0)),0.0)

-}

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

add' :: Exp a -> Exp a
add' = App (Primitive Add)

mul' :: Exp a -> Exp a
mul' = App (Primitive Mul)

id' :: Exp a
id' = Lam () (Var (Right ()))

-- (a -> b) -> (b -> c) -> (a -> c)
sequenceD :: Exp a -> Exp a -> Exp a
sequenceD (Diff tx f) (Diff ty g) = Diff (Tuple tx ty) $ Lam () body
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
    a = Var (Right ())
    b = fst' (Var (Right ()))
    c = fst' (Var (Right ()))
    body =
      let' (App (shift f) a) $
        let' (App (shift $ shift g) b) (Tuple c (Lam () pullback))
    g' = snd' (Var (Left (Right ())))
    f' = snd' (Var (Left $ Left $ Left (Right ())))
    db = snd' (Var (Right ()))
    x = fst' (Var (Right ()))
    y = fst' (Var (Left (Right ())))
    da = snd' (Var (Right ()))
    pullback = let' (App g' (Var (Right ()))) $ let' (App f' db) (Tuple (Tuple x y) da)
sequenceD _ _ = error "Cannot sequence"

-- (a -> b) -> (a -> c) -> (a -> (b,c))
fanOut :: Exp a -> Exp a -> Exp a
fanOut f g = sequenceD dupD (parallelD f g)

dupD :: Exp a
dupD = Diff (Type TUnit) $ Lam () (Tuple (Tuple a a) pullback)
  where
    {-
       dupD = \a -> ((a,a), \(da,db) -> ((), add (da,db)))
    -}
    a = Var (Right ())
    p = Var (Right ())
    pullback = Lam () (Tuple Unit (add' p))

parallelD :: Exp a -> Exp a -> Exp a
parallelD (Diff tx f) (Diff ty g) = Diff (Tuple tx ty) $ Lam () body
  where
    {-
       parallelD f g = \(a,c) ->
        let ((b, f'), (d,g')) = (f a, g c)
        in ((b,d) \(db, dd) ->
          let ((x,da), (y, dc)) = (f' db, g' dd)
          in ((x,y), (da,dc))
        )
    -}
    a = fst' (Var (Right ()))
    c = snd' (Var (Right ()))
    b = fst' $ fst' (Var (Right ()))
    d = fst' $ snd' (Var (Right ()))
    body =
      let' (Tuple (App (shift f) a) (App (shift g) c)) $
        Tuple (Tuple b d) (Lam () pullback)
    f' = snd' $ fst' $ Var $ Left (Right ())
    g' = snd' $ snd' $ Var $ Left (Right ())
    db = fst' (Var (Right ()))
    dd = snd' (Var (Right ()))
    x = fst' $ fst' (Var (Right ()))
    da = snd' $ fst' (Var (Right ()))
    y = fst' $ snd' (Var (Right ()))
    dc = snd' $ snd' (Var (Right ()))
    pullback =
      let' (Tuple (App f' db) (App g' dd)) $
        Tuple (Tuple x y) (Tuple da dc)
parallelD _ _ = error "Cannot parallel"

-- (a -> b, a) -> b
applyD :: Exp a
applyD = Diff (Type TUnit) $ Lam () body
  where
    {-
       applyD = \(f,a) ->
        let (b,f') = f a
        in (b, \db -> ((), f' db))
    -}
    f = fst' (Var (Right ()))
    a = snd' (Var (Right ()))
    b = fst' (Var (Right ()))
    body = let' (App f a) (Tuple b (Lam () pullback))
    f' = snd' $ Var (Left (Right ()))
    db = Var (Right ())
    pullback = Tuple (Type TUnit) (App f' db)

letCase :: Pattern b -> Exp v -> Exp (Either v b) -> Exp v
letCase p x body = App (LamCase p () body) x

-- (x,(da,db)) |-> ((x,da),db)
reassoc :: Exp (Either v ())
reassoc =
  let p = Var (Right ())
      x = fst' p
      da = fst' (snd' p)
      db = snd' (snd' p)
   in Tuple (Tuple x da) db

-- >>> named (Lam () $ Lam () $ (Var (Right ())))
-- Lam x0 (Lam x1 (Var (Left (Left "x1"))))
named :: Exp Void -> Exp' String String
named expr = name absurd expr 0
  where
    name :: (a -> String) -> Exp a -> Int -> Exp' String String
    name g (Lam _ body) n = Lam ("x" <> show n) $ Left <$> name (withName g) body (succ n)
      where
        withName :: (a -> String) -> Either a () -> String
        withName h (Left x) = h x
        withName _ (Right ()) = "x" <> show n
    name g (LamCase p _ body) n = LamCase p (vars p n) $ Left <$> name (withName g p n) body (n + bound p)
      where
        vars :: Pattern b -> Int -> String
        vars IgnoreCase _ = "_"
        vars VarCase m = "x" <> show m
        vars (TupleCase a b) m = "(" <> vars a m <> "," <> vars b (m + bound a) <> ")"
        withName :: (x -> String) -> Pattern b -> Int -> Either x b -> String
        withName h _ _ (Left x) = h x
        withName _ IgnoreCase _ (Right void) = case void of
        withName _ VarCase m (Right ()) = "x" <> show m
        withName h (TupleCase a b) m (Right p') =
          case p' of
            Left x -> withName h a m (Right x)
            Right x -> withName h b (bound a + m) (Right x)
        bound :: Pattern a -> Int
        bound IgnoreCase = 0
        bound VarCase = 1
        bound (TupleCase a b) = bound a + bound b
    name g (Var x) _ = Var (g x)
    name g (App f x) n = App (name g f n) (name g x n)
    name g (Diff t x) n = Diff (name g t n) (name g x n)
    name g (Tuple a b) n = Tuple (name g a n) (name g b n)
    name _ Unit _ = Unit
    name _ (Const x) _ = Const x
    name g (Zero x) n = Zero (name g x n)
    name _ (Primitive p) _ = Primitive p
    name _ (Type t) _ = Type t
    name g (Tangent t) n = Tangent (name g t n)

{-
    -}

-- ((a,b) -> c) -> (a -> (b -> c))
-- (dc -> (dx, (da, db))) (a,b) -> c : Tan c = dc
-- (dc -> ((dx, da), db) b -> c : Tan (b -> c) = (dx, da)
-- ((dx, da) -> (dx, da)) (a -> (b -> c))
-- FIXME: curryD should return a differentiable function (with tangent type) and not a plain lambda
curryD :: Show a => Exp a -> Exp a
curryD (Diff tx f) =
  Diff tx $
    Lam () $
      let g =
            Lam () $
              let a = Var (Left (Right ()))
                  b = Var (Right ())
               in let' (App (shift $ shift f) (Tuple a b)) $
                    let c = fst' (Var (Right ()))
                     in Tuple c $
                          Lam () $
                            let dc = Var $ Right ()
                                f' = snd' $ Var $ Left (Right ())
                             in let' (App f' dc) reassoc
       in let' (Diff (Tuple (shift tx) (Tangent (Var (Right ())))) g) (Tuple (Var (Right ())) id')
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
        in (Diff (tx, tangentOf a) g, \r -> r)

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
uncurryD (Diff tx f) = Diff tx $ Lam () body
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
      let' (App (shift f) (fst' (Var (Right ())))) $
        let' (App (fst' (Var (Right ()))) (snd' (Var (Left (Right ()))))) $
          Tuple (fst' (Var (Right ()))) (Lam () pullback)
    g' = snd' $ Var $ Left $ Right ()
    dc = Var $ Right ()
    f' = snd' $ Var $ Left $ Left $ Left $ Right ()
    y = fst' $ Var (Right ())
    x = fst' $ Var (Right ())
    da = snd' $ Var (Right ())
    db = snd' $ Var (Left $ Right ())
    pullback =
      let' (App g' dc) $
        let' (App f' y) $
          Tuple x (Tuple da db)
uncurryD _ = error "uncurry: Not a diff function"

fstD :: Exp a
fstD = Diff (Type TUnit) $ Lam () body
  where
    {-
       fstD = \(a,b) -> (a, \da -> ((), (da, zero b)))
    -}
    b = snd' (Var (Left (Right ())))
    pullback = Tuple Unit (Tuple (Var (Right ())) (Zero b))
    a = fst' (Var (Right ()))
    body = Tuple a (Lam () pullback)

sndD :: Exp a
sndD = Diff (Type TUnit) $ Lam () body
  where
    {-
       sndD = \(a,b) -> (b, \db -> ((), (zero a, db)))
    -}
    a = fst' (Var (Left (Right ())))
    pullback = Tuple Unit (Tuple (Zero a) (Var (Right ())))
    b = snd' (Var (Right ()))
    body = Tuple b (Lam () pullback)

addD :: Exp a
addD = Diff (Type TUnit) $ Lam () body
  where
    {-
       addD = \(a,b) -> (a + b, \dc -> ((), (dc, dc)))
    -}
    pullback = Tuple (Type TUnit) (Tuple (Var (Right ())) (Var (Right ())))
    body = Tuple (add' (Var (Right ()))) (Lam () pullback)

mulD :: Exp a
mulD = Diff (Type TUnit) $ Lam () body
  where
    {-
       mulD = \(a,b) -> (a * b, \dc -> ((), (b * dc, a * dc)))
    -}
    dc = Var (Right ())
    a = fst' (Var (Left (Right ())))
    b = snd' (Var (Left (Right ())))
    pullback = Tuple (Type TUnit) (Tuple (mul' (Tuple b dc)) (mul' (Tuple a dc)))
    body = Tuple (mul' (Var (Right ()))) (Lam () pullback)
