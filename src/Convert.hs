{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Convert where

import Data.Void (Void, absurd)
import Prettyprinter (Doc, Pretty (..), hsep, nest, parens, viaShow, vsep)

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
  pretty (Precedence _ (Tuple f x)) = pretty (Precedence 0 f, Precedence 0 x)
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
  ( Mul Left ()
  , λ
    ( Unit
    , ( Mul (Snd Right (Left ()), Left ())
    , Mul (Fst Right (Left ()), Left ()) ) ) )

>>> pretty (convert IgnoreCase (Primitive Add) :: Exp Void)
λ
  (Add Left (), λ (Unit, (Left (), Left ())))

>>> pretty (convert IgnoreCase (Primitive Fst) :: Exp Void)
λ
  (Fst Left (), λ (Unit, (Left (), zero (Snd Right (Left ())))))

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
  | Apply
  | DiffArrow Type Arrow
  | ConstArrow Float
  | UnitArrow
  | Duplicate
  | PrimArrow Prim
  | NoDiff (Exp Void)
  deriving (Show)

instance Pretty (Precedence Arrow) where
  pretty (Precedence _ Identity) = pretty "id"
  pretty (Precedence d (Sequence f g)) = parens' 6 d $ hsep [pretty (Precedence 6 f), pretty ">>>", pretty (Precedence 6 g)]
  pretty (Precedence d (Parallel f g)) = parens' 7 d $ hsep [pretty (Precedence 7 f), pretty "⊗", pretty (Precedence 7 g)]
  pretty (Precedence d (Curry f)) = parens' 10 d $ hsep [pretty "curry", pretty (Precedence 11 f)]
  pretty (Precedence d (Uncurry f)) = parens' 10 d $ hsep [pretty "uncurry", pretty (Precedence 11 f)]
  pretty (Precedence d (DiffArrow _ arr)) = pretty (Precedence d arr)
  pretty (Precedence _ Apply) = pretty "apply"
  pretty (Precedence d (ConstArrow x)) = parens' 10 d $ hsep [pretty "const", pretty x]
  pretty (Precedence _ UnitArrow) = pretty ()
  pretty (Precedence _ Duplicate) = pretty "dup"
  pretty (Precedence _ (PrimArrow p)) = viaShow p
  pretty (Precedence d (NoDiff expr)) = pretty (Precedence d expr)

instance Pretty Arrow where
  pretty x = pretty (Precedence 0 x)

{-
>>> pretty $ diffArrow' (PrimArrow Fst)
λ
  (Fst Left (), λ (Unit, (Left (), zero (Snd Right (Left ())))))

>>> pretty $ diffArrow' (PrimArrow Add)
λ
  (Add Left (), λ (Unit, (Left (), Left ())))

>>> pretty $ diffArrow' (PrimArrow Mul)
λ
  ( Mul Left ()
  , λ
    ( Unit
    , ( Mul (Snd Right (Left ()), Left ())
    , Mul (Fst Right (Left ()), Left ()) ) ) )

>>> pretty $ diffArrow' Duplicate
λ
  ((Left (), Left ()), λ (Unit, Add Left ()))

>>> pretty $ diffArrow' UnitArrow
λ
  (Unit, λ (Unit, zero Right (Left ())))

\a -> ((), \da -> ((), zero a))

>>> pretty $ diffArrow' (Curry Identity)
λ
  (λ
    (Left (), λ Left ())) (λ
    (λ(x, x)
      ( Right (Left ())
      , λ
        (λ(x, (x, x))
          ( (Left (Right ()), Left (Left (Right ())))
          , Left (Left (Left ())) )) (Right (Left (Left ())) Left ()) )) ((λ
      (Left (), λ (Unit, Left ()))) (Right (Left ()), Left ())))

λa
  (λb
    (b, λc c)) (λd
    (λe
      ( Fst e
      , λf
        (λg
          ( (Fst g, Fst (Snd g))
          , Snd (Snd g) )) ((Snd f) f) )) ((λh
      (h, λi (Unit, i))) (d, e)))

>>> pretty $ diffArrow' (Curry (NoDiff (Primitive Add)))
λ
  (λ
    (Left (), λ Left ())) (λ
    (λ(x, x)
      ( Right (Left ())
      , λ
        (λ(x, (x, x))
          ( (Left (Right ()), Left (Left (Right ())))
          , Left (Left (Left ())) )) (Right (Left (Left ())) Left ()) )) (Add ( Right (Left ())
    , Left () )))

λa (λg (g, λr r))
    (λb
      (λ
        ( Fst Left ()
        , λ
          (λ
            ( (Fst Left (), Fst (Snd Left ()))
            , Snd (Snd Left ()) )) ((Snd Right (Left ())) Left ()) )
      ) (Add ( Right (Left ()) , Left () ))
    )

-}
diffArrow :: Arrow -> Exp o
diffArrow Identity = idD
diffArrow (Sequence f g) = sequenceD (diffArrow f) (diffArrow g)
diffArrow (Parallel f g) = parallelD (diffArrow f) (diffArrow g)
diffArrow (Curry f) = curryD (diffArrow f)
diffArrow (Uncurry f) = uncurryD (diffArrow f)
diffArrow Apply = applyD
diffArrow (DiffArrow t f) = Diff t (diffArrow f)
diffArrow Duplicate = dupD
diffArrow (ConstArrow x) = constD (Const x)
diffArrow UnitArrow = constD Unit
diffArrow (PrimArrow Fst) = fstD
diffArrow (PrimArrow Snd) = sndD
diffArrow (PrimArrow Add) = addD
diffArrow (PrimArrow Mul) = mulD
diffArrow (NoDiff expr) = Diff TUnit (fmap absurd expr)

diffArrow' :: Arrow -> Exp Void
diffArrow' = diffArrow

fanOutArrow :: Arrow -> Arrow -> Arrow
fanOutArrow f g = Sequence Duplicate (Parallel f g)

convertArrow :: Pattern b -> Exp b -> Arrow
convertArrow ctx (Lam body) = Curry $ convertArrow (TupleCase ctx VarCase) body
convertArrow ctx (LamCase p body) = Curry $ convertArrow (TupleCase ctx p) body
convertArrow ctx (Var i) = convertVar ctx i
convertArrow ctx (App f x) = (convertArrow ctx f `fanOutArrow` convertArrow ctx x) `Sequence` Apply
convertArrow ctx (Tuple a b) = convertArrow ctx a `fanOutArrow` convertArrow ctx b
convertArrow ctx (Diff x expr) = DiffArrow x (convertArrow ctx expr) -- TODO: is it true that the tangent of the second order is the same as the first order?
convertArrow _ (Zero _) = error "Cannot differentiate zero (yet?)" -- Zero is a constant, should have zero gradient of the same shape
convertArrow _ Unit = UnitArrow
convertArrow _ (Const x) = ConstArrow x
convertArrow _ (Primitive p) = Sequence UnitArrow (constFun (PrimArrow p))

-- constFun :: (b `k` c) -> (a `k` (b :=> c))
constFun :: Arrow -> Arrow
constFun f = Curry (Sequence (PrimArrow Snd) f)

-- unitFun :: (b `k` c) -> (() `k` (b :=> c))
unitFun :: Arrow -> Arrow
unitFun = constFun

convert :: Pattern b -> Exp b -> Exp o
convert ctx = diffArrow . convertArrow ctx

optimizeArrow :: Arrow -> Arrow
optimizeArrow (Uncurry (Curry f)) = optimizeArrow f
optimizeArrow (Uncurry f) = Uncurry (optimizeArrow f)
optimizeArrow (Curry (Uncurry f)) = optimizeArrow f
optimizeArrow (Curry f) = Curry $ optimizeArrow f
optimizeArrow (Sequence Identity f) = optimizeArrow f
optimizeArrow (Sequence f Identity) = optimizeArrow f
optimizeArrow (Sequence f g) = Sequence (optimizeArrow f) (optimizeArrow g)
optimizeArrow (Sequence (Parallel f g) (Parallel x y)) = Parallel (optimizeArrow $ Sequence f x) (optimizeArrow $ Sequence g y)
optimizeArrow (Parallel (PrimArrow Fst) (PrimArrow Snd)) = Identity
optimizeArrow (Parallel f g) = Parallel (optimizeArrow f) (optimizeArrow g)
optimizeArrow Identity = Identity
optimizeArrow Apply = Apply
optimizeArrow (DiffArrow t arr) = DiffArrow t (optimizeArrow arr)
optimizeArrow (ConstArrow x) = ConstArrow x

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

{-
>>> pretty $ convert' (Primitive Add)
λ
  (λ
    (λ
      ( Fst Left ()
      , λ
        (λ
          (λ
            ( (Fst Left (), Fst Right (Left ()))
            , Snd Left () )) ((Snd Right (Right (Right (Right (Left ()))))) (Snd Left ()))) ((Snd Right (Right (Left ()))) Left ()) )) ((λ
      (λ
        (λ
          ( Fst Left ()
          , λ
            (λ
              (λ
                ( Fst Left ()
                , ( Snd Left ()
                , Snd Right (Left ()) ) )) ((Snd Right (Right (Right (Left ())))) (Fst Left ()))) ((Snd Right (Left ())) Left ()) )) ((Fst Left ()) (Snd Right (Left ())))) ((λ
        (λ
          (λ
            ( Fst Left ()
            , λ
              (λ
                (λ
                  ( (Fst Left (), Fst Right (Left ()))
                  , Snd Left () )) ((Snd Right (Right (Right (Right (Left ()))))) (Snd Left ()))) ((Snd Right (Right (Left ()))) Left ()) )) ((λ
            (λ
              (Left (), λ Left ())) (λ
              (λ(x, x)
                ( Right (Left ())
                , λ
                  (λ(x, (x, x))
                    ( (Left (Right ()), Left (Left (Right ())))
                    , Left (Left (Left ())) )) (Right (Left (Left ())) Left ()) )) ((λ
                (λ
                  (λ
                    ( Fst Left ()
                    , λ
                      (λ
                        (λ
                          ( (Fst Left (), Fst Right (Left ()))
                          , Snd Left () )) ((Snd Right (Right (Right (Right (Left ()))))) (Snd Left ()))) ((Snd Right (Right (Left ()))) Left ()) )) ((λ
                    ( Add Left ()
                    , λ
                      (Unit, (Left (), Left ())) )) (Fst Left ()))) ((λ
                  ( Snd Left ()
                  , λ
                    ( Unit
                    , ( zero (Fst Right (Left ()))
                    , Left () ) ) )) Left ())) ( Right (Left ())
              , Left () )))) (Fst Left ()))) ((λ
          ( Unit
          , λ
            ( Unit
            , zero Right (Left ()) ) )) Left ())) (Fst Left ()))) (Fst Left ()))) ((λ
    (λ
      (λ
        ( Fst Left ()
        , λ
          (λ
            (λ
              ( (Fst Left (), Fst Right (Left ()))
              , Snd Left () )) ((Snd Right (Right (Right (Right (Left ()))))) (Snd Left ()))) ((Snd Right (Right (Left ()))) Left ()) )) ((λ
        (λ
          (λ
            ( (Fst Right (Left ()), Fst Left ())
            , λ
              (λ
                (λ
                  ( (Fst Right (Left ()), Fst Left ())
                  , ( Snd Right (Left ())
                  , Snd Left () ) )) (Right (Right (Left ())) (Snd Right (Left ())))) (Right (Right (Left ())) (Fst Left ())) )) ((λ
            (Left (), λ (Unit, Left ()))) (Snd Left ()))) ((λ
          ( Unit
          , λ
            (Unit, zero Right (Left ())) )) (Fst Left ()))) (Fst Left ()))) ((λ
      ((Left (), Left ()), λ (Unit, Add Left ()))) Left ())) Left ())

>>> callD (evalD (convert' (Primitive Add))) (Pair (Number 2) (Number 4)) (Number 5)
Cannot call non-function

>>> pretty $ convertArrow IgnoreCase $ Const 2
const 2.0

>>> pretty $ convertArrow IgnoreCase $ (Lam (Const 2))
curry (const 2.0)

>>> pretty $ convertArrow' (Lam (Const 3))
dup >>> () ⊗ id >>> uncurry (curry (const 3.0))

>>> callD (evalD (convert' (Lam (Const 2)))) (Number 4) (Number 5)
Cannot get snd of non-pair

>>> pretty $ convertArrow IgnoreCase (Tuple (Const 2) (Const 3))
dup >>> const 2.0 ⊗ const 3.0

>>> pretty $ convertArrow' (Lam $ App (Primitive Add) (Tuple (Const 2) (Const 3)))
dup >>> () ⊗ id >>> uncurry (curry (dup >>> (() >>> curry (Snd >>> Add)) ⊗ (dup >>> const 2.0 ⊗ const 3.0) >>> apply))

>>> pretty $ convertArrow IgnoreCase (App (Primitive Add) (Tuple (Const 2) (Const 3)))
dup >>> (() >>> curry (Snd >>> Add)) ⊗ (dup >>> const 2.0 ⊗ const 3.0) >>> apply

>>> callD (evalD $ convert' (Primitive Add)) (Number 2) (Number 3)
Cannot get snd of non-pair

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
              _ -> error "Not a tangent"
        )
      _ -> error "Not a diff result"
  _ -> error "Not a diff function"

data Context v where
  EmptyContext :: Context Void
  Bind :: Value -> Context v -> Context (Either () v)
  BindPair :: Context a -> Context b -> Context (Either a b)

eval :: Show v => Context v -> Exp v -> Value
eval ctx (Lam e) = Closure $ \a -> eval (Bind a ctx) e
eval ctx (LamCase p e) = Closure $ \a ->
  showPattern p $
    let x = patternMatch a p
     in eval (BindPair x ctx) e
  where
    patternMatch :: Value -> Pattern b -> Context b
    patternMatch = undefined
eval ctx (Var i) = lookupVar ctx i
  where
    lookupVar :: Context x -> x -> Value
    lookupVar EmptyContext v = case v of
    lookupVar (Bind a _) (Left ()) = a
    lookupVar (Bind _ as) (Right v) = lookupVar as v
    lookupVar (BindPair as _) (Left v) = lookupVar as v
    lookupVar (BindPair _ bs) (Right v) = lookupVar bs v
eval ctx (App f x) =
  case (eval ctx f, eval ctx x) of
    (Closure vf, v) -> vf v
    _ -> error "Cannot call non-function"
eval ctx (Tuple a b) = Pair (eval ctx a) (eval ctx b)
eval _ Unit = UnitValue
eval _ (Const x) = Number x
eval _ (Primitive Fst) = Closure go
  where
    go (Pair a _) = a
    go _ = error "Cannot get fst of non-pair"
eval _ (Primitive Snd) = Closure go
  where
    go (Pair _ b) = b
    go _ = error "Cannot get snd of non-pair"
eval _ (Primitive Add) = Closure go
  where
    go (Pair (Number a) (Number b)) = Number $ a + b
    go (Pair UnitValue UnitValue) = UnitValue
    go x = error $ "Cannot add" <> show x
eval _ (Primitive Mul) = Closure go
  where
    go (Pair (Number a) (Number b)) = Number $ a * b
    go (Pair UnitValue UnitValue) = UnitValue
    go _ = error "Cannot multiply"
eval ctx (Zero expr) =
  case eval ctx expr of
    Pair (TypeValue t) (Closure _) -> zeroTangent t
    Number _ -> Number 0
    UnitValue -> UnitValue
    _ -> error $ "No zero for" <> show expr
eval ctx (Diff t expr) = Pair (TypeValue t) (eval ctx expr)

zeroTangent :: Type -> Value
zeroTangent TFloat = Number 0
zeroTangent (TTuple a b) = Pair (zeroTangent a) (zeroTangent b)
zeroTangent (TArr _ _) = error "No tangent for function"
zeroTangent TUnit = UnitValue

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
dup >>> () ⊗ id >>> uncurry (() >>> curry (Snd >>> Add))
-}
add' :: Exp a -> Exp a
add' = App (Primitive Add)

mul' :: Exp a -> Exp a
mul' = App (Primitive Mul)

id' :: Exp a
id' = Lam (Var (Left ()))

-- (a -> b) -> (b -> c) -> (a -> c)
sequenceD :: forall a. Exp a -> Exp a -> Exp a
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
    g' = snd' (Var (Right $ Right (Left ())))
    f' = snd' (Var (Right $ Right $ Right $ Right (Left ())))
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
        let (b, f') = f a
            (d, g') = g c
        in ((b,d) \(db, dd) ->
          let (x,da) = f' db
              (y,dc) = g' dd
          in ((x,y), (da,dc))
        )
    -}
    a = fst' (Var (Left ()))
    c = snd' (Var (Left ()))
    b = fst' (Var (Right (Left ())))
    d = fst' (Var (Left ()))
    body =
      let' (App (shift f) a) $
        let' (App (shift $ shift g) c) $
          Tuple (Tuple b d) (Lam pullback)
    f' = Var $ Right $ Right (Left ())
    g' = Var $ Right $ Right (Left ())
    db = fst' (Var (Left ()))
    dd = snd' (Var (Right (Left ())))
    x = fst' (Var (Right (Left ())))
    da = snd' (Var (Right (Left ())))
    y = fst' (Var (Left ()))
    dc = snd' (Var (Left ()))
    pullback =
      let' (App f' db) $
        let' (App g' dd) $
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
curryD :: Exp a -> Exp a
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
curryD _ = error "No curry"

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
