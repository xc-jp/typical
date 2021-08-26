{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Exp where

import Control.Applicative (Applicative (liftA2))
import Control.Category (Category (..), (>>>))
import Data.Data (Proxy (Proxy))
import Data.Kind (Type)
import Data.Type.Equality (TestEquality (..), (:~:) (..))
import Numeric.Natural (Natural)
import Prelude hiding (id, (.))

data Index ctx t where
  IZ :: Index (x ': xs) x
  IS :: Index xs x -> Index (y ': xs) x

-- | Pattern match cases for LamCase rule
-- The Lam rule is equivalent to LamCase VarCase
data Pattern bound t where
  UnitCase :: Pattern '[] ()
  VarCase :: Pattern '[t] t
  TupleCase :: Pattern xs a -> Pattern ys b -> Pattern (xs ++ ys) (a, b)
  ConsCase :: Pattern xs (Vec n a) -> Pattern (a ': xs) (Vec ('Succ n) a)
  NilCase :: Pattern '[] (Vec 'Zero a)

data Exp ctx t where
  Var :: Index ctx a -> Exp ctx a
  Lam :: Exp (a ': ctx) b -> Exp ctx (a -> b)
  LamCase :: Pattern bound a -> Exp (bound ++ ctx) b -> Exp ctx (a -> b)
  App :: Exp ctx (a -> b) -> Exp ctx a -> Exp ctx b
  Constant :: a -> Exp ctx a
  -- TODO: Move these into primitives?
  Tuple :: Exp ctx a -> Exp ctx b -> Exp ctx (a, b)
  At :: Fin n -> Exp ctx (Vec n a) -> Exp ctx a
  Construct :: Vec n (Exp ctx a) -> Exp ctx (Vec n a)

-- TODO: Need types like tensor here
data Ty = TyFloat | TyPair Ty Ty | TyArr Ty Ty | TyVec Natural Ty | TyUnit

data Typ t where
  TypFloat :: Typ Float
  TypUnit :: Typ ()
  TypPair :: Typ a -> Typ b -> Typ (a, b)
  TypArr :: Typ a -> Typ b -> Typ (a -> b)
  TypVec :: Vec n () -> Typ a -> Typ (Vec n a)

instance TestEquality Typ where
  testEquality TypFloat TypFloat = Just Refl
  testEquality TypFloat _ = Nothing
  testEquality TypUnit TypUnit = Just Refl
  testEquality TypUnit _ = Nothing
  testEquality (TypPair a b) (TypPair c d) = do
    Refl <- testEquality a c
    Refl <- testEquality b d
    pure Refl
  testEquality TypPair {} _ = Nothing
  testEquality (TypArr a b) (TypArr c d) = do
    Refl <- testEquality a c
    Refl <- testEquality b d
    pure Refl
  testEquality TypArr {} _ = Nothing
  testEquality (TypVec n x) (TypVec m y) = do
    Refl <- testEquality x y
    Refl <- equalLength n m
    pure Refl
  testEquality TypVec {} _ = Nothing

equalLength :: Vec n () -> Vec m () -> Maybe (n :~: m)
equalLength Nil Nil = Just Refl
equalLength Nil Cons {} = Nothing
equalLength Cons {} Nil = Nothing
equalLength (Cons _ xs) (Cons _ ys) = do
  Refl <- equalLength xs ys
  pure Refl

vecOf :: Natural -> (forall n. Vec n () -> r) -> r
vecOf 0 k = k Nil
vecOf n k = vecOf (pred n) $ \v -> k (Cons () v)

reifyType :: Ty -> (forall t. Typ t -> r) -> r
reifyType TyFloat k = k TypFloat
reifyType TyUnit k = k TypUnit
reifyType (TyPair a b) k =
  reifyType a $ \ta ->
    reifyType b $ \tb ->
      k $ TypPair ta tb
reifyType (TyArr dom cod) k =
  reifyType dom $ \ta ->
    reifyType cod $ \tb ->
      k (TypArr ta tb)
reifyType (TyVec n a) k =
  reifyType a $ \ta ->
    vecOf n $ \v ->
      k (TypVec v ta)

forgetType :: Typ t -> Ty
forgetType TypFloat = TyFloat
forgetType TypUnit = TyUnit
forgetType (TypPair a b) = TyPair (forgetType a) (forgetType b)
forgetType (TypArr a b) = TyArr (forgetType a) (forgetType b)
forgetType (TypVec v a) = TyVec (vLen v) (forgetType a)
  where
    vLen :: Vec n x -> Natural
    vLen Nil = 0
    vLen (Cons _ vs) = succ (vLen vs)

-- TODO: Error messages for the type errors
-- TODO: Infer types of lambdas based on primitives
typecheck :: UExp -> (forall t. Typ t -> Exp '[] t -> Maybe r) -> Maybe r
typecheck = go Nil'
  where
    go :: List Typ ctx -> UExp -> (forall t. Typ t -> Exp ctx t -> Maybe r) -> Maybe r
    go ctx (UVar n) k = checkVar ctx n $ \t i -> k t (Var i)
    go ctx (ULam t expr) k =
      reifyType t $ \ta ->
        go (Cons' ta ctx) expr $ \tb body -> k (TypArr ta tb) (Lam body)
    go ctx (ULamCase t upat expr) k =
      reifyType t $ \ta ->
        checkPattern ta upat $ \bound pat ->
          go (concatList bound ctx) expr $ \tb body ->
            k (TypArr ta tb) (LamCase pat body)
    go ctx (UApp f x) k =
      go ctx f $ \tg g ->
        go ctx x $ \ta y ->
          case tg of
            TypArr ta' tb -> do
              Refl <- testEquality ta ta'
              k tb (App g y)
            _ -> Nothing
    go _ (ULit (LitFloat x)) k = k TypFloat (Constant x)
    go ctx (UTuple a b) k =
      go ctx a $ \ta x ->
        go ctx b $ \tb y ->
          k (TypPair ta tb) (Tuple x y)

-- | Needs to be checkPattern because we don't know the context for VarCase
-- unless we already know the type of the variable
checkPattern :: Typ a -> UPattern -> (forall bound. List Typ bound -> Pattern bound a -> Maybe r) -> Maybe r
checkPattern t UUnitCase k = do
  Refl <- testEquality t TypUnit
  k Nil' UnitCase
checkPattern t UVarCase k = k (Cons' t Nil') VarCase
checkPattern (TypPair ta tb) (UTupleCase a b) k =
  checkPattern ta a $ \as pa ->
    checkPattern tb b $ \bs pb ->
      k (concatList as bs) (TupleCase pa pb)
checkPattern _ (UTupleCase _ _) _ = Nothing
checkPattern (TypVec (Cons _ v) ta) (UConsCase rest) k =
  checkPattern (TypVec v ta) rest $ \ctx prest ->
    k (Cons' ta ctx) (ConsCase prest)
checkPattern _ UConsCase {} _ = Nothing
checkPattern (TypVec Nil _) UNilCase k = k Nil' NilCase
checkPattern _ UNilCase _ = Nothing

checkVar :: List Typ ctx -> Int -> (forall t. Typ t -> Index ctx t -> Maybe r) -> Maybe r
checkVar Nil' _ _ = Nothing -- index out of bounds
checkVar (Cons' t _) 0 k = k t IZ
checkVar (Cons' _ ts) n k = checkVar ts (pred n) $ \t i -> k t (IS i)

newtype Literal = LitFloat Float

data UPattern
  = UUnitCase
  | UVarCase
  | UTupleCase UPattern UPattern
  | UConsCase UPattern
  | UNilCase

data UExp
  = UVar Int
  | ULam Ty UExp
  | ULamCase Ty UPattern UExp
  | UApp UExp UExp
  | ULit Literal
  | UTuple UExp UExp

data Arrow :: (* -> * -> *) -> * -> * -> * where
  -- | Category
  Identity :: Arrow p a a
  Sequence :: Arrow p a b -> Arrow p b c -> Arrow p a c
  -- | Monoidal
  Parallel :: Arrow p a b -> Arrow p c d -> Arrow p (p a c) (p b d)
  -- | Cartesian
  Exl :: Arrow p (p a b) a
  Exr :: Arrow p (p a b) b
  Dup :: Arrow p a (p a a)
  It :: Arrow p a ()
  -- | Cocartesian
  Inl :: Arrow p a (p a b)
  Inr :: Arrow p b (p a b)
  Jam :: Arrow p (p a a) a
  -- | Exponentials (first-class functions)
  Curry :: Arrow p (p a b) c -> Arrow p a (b -> c)
  Uncurry :: Arrow p a (b -> c) -> Arrow p (p a b) c
  -- | Primitive values (unconstrained for now to match Constant)
  -- TODO: Constrain constants to some data type of primitives
  Const :: b -> Arrow p a b
  -- | Vec arrows (TODO: move these into primitives)
  Head :: Arrow p (Vec ('Succ n) a) a
  Tail :: Arrow p (Vec ('Succ n) a) (Vec n a)
  ParVec :: Vec n (Arrow p a b) -> Arrow p (Vec n a) (Vec n b)
  DupVec :: KnownNat n => Arrow p a (Vec n a)
  JamVec :: Arrow p (Vec n a) a

instance Category (Arrow p) where
  id = Identity
  Identity . f = f
  f . Identity = f
  Exl . Inl = Identity
  Exr . Inr = Identity
  Jam . Dup = Identity
  Exl . (Sequence Dup (Parallel f _)) = f
  Exr . (Sequence Dup (Parallel _ g)) = g
  It . _ = It
  Sequence (Parallel f _) Jam . Inl = f
  Sequence (Parallel _ g) Jam . Inr = g
  Parallel Exl Exr . Dup = Identity
  Sequence g h . f = h . (g . f)
  Parallel f g . Parallel x y = Parallel (f . x) (g . y)
  g . f = Sequence f g

-- | Apply unit to the
runArrow :: Arrow (,) () (a -> b) -> Arrow (,) a b
runArrow g = It `fanOut` Identity >>> Uncurry g

apply :: Arrow p (p (b -> c) b) c
apply = Uncurry Identity

fanOut :: Arrow p a b -> Arrow p a c -> Arrow p a (p b c)
fanOut f g = Dup >>> Parallel f g

fanOutVec :: Vec n (Arrow p a b) -> Arrow p a (Vec n b)
fanOutVec vs = knownVec vs $ DupVec >>> ParVec vs
  where
    knownVec :: Vec n x -> (KnownNat n => r) -> r
    knownVec Nil ok = ok
    knownVec (Cons _ xs) ok = knownVec xs ok

fanIn :: Arrow p b a -> Arrow p c a -> Arrow p (p b c) a
fanIn f g = Parallel f g >>> Jam

toArrow :: Exp '[] a -> Arrow (,) () a
toArrow expr = convert expr UnitCase

toArrow' :: Exp '[] (a -> b) -> Arrow (,) a b
toArrow' = runArrow . toArrow

listNil :: Length xs -> ((xs ++ '[]) ~ xs => r) -> r
listNil LZ ok = ok
listNil (LS l) ok = listNil l ok

swap :: Arrow p (p a b) (p b a)
swap = Dup >>> Parallel Exr Exl

convert :: Exp bound b -> Pattern bound a -> Arrow (,) a b
convert (Var i) p = convertVar p i
convert (LamCase q body) p = Curry $ swap >>> convert body (TupleCase q p)
convert (App f x) p = convert f p `fanOut` convert x p >>> apply
convert (Lam body) p = Curry $ swap >>> convert body (TupleCase VarCase p)
convert (At n expr) p = convert expr p >>> at n
  where
    at :: Fin n -> Arrow (,) (Vec n a) a
    at FZ = Head
    at (FS i) = Sequence Tail (at i)
convert (Construct Nil) _ = Const Nil
convert (Construct vs) p = fanOutVec $ fmap (`convert` p) vs
convert (Tuple a b) p = convert a p `fanOut` convert b p
convert (Constant x) _ = Const x

absurdIndex :: Index '[] a -> b
absurdIndex i = case i of

type family Len (xs :: [k]) :: Nat where
  Len '[] = 'Zero
  Len (_ ': xs) = 'Succ (Len xs)

convertVar :: Pattern bound a -> Index bound b -> Arrow (,) a b
convertVar VarCase IZ = Identity
convertVar VarCase (IS i) = absurdIndex i
convertVar UnitCase i = absurdIndex i
convertVar (TupleCase a b) is =
  case splitIndex (boundLength a) is of
    Left i -> Exl >>> convertVar a i
    Right i -> Exr >>> convertVar b i
convertVar NilCase i = absurdIndex i
convertVar (ConsCase _) IZ = Head
convertVar (ConsCase vs) (IS i) = Sequence Tail (convertVar vs i)

splitIndex :: Length xs -> Index (xs ++ ys) t -> Either (Index xs t) (Index ys t)
splitIndex LZ i = Right i
splitIndex (LS _) IZ = Left IZ
splitIndex (LS xs) (IS i) = case splitIndex xs i of
  Left j -> Left (IS j)
  Right j -> Right j

concatLength :: Length xs -> Length ys -> Length (xs ++ ys)
concatLength LZ ys = ys
concatLength (LS xs) ys = LS (concatLength xs ys)

boundLength :: Pattern xs t -> Length xs
boundLength UnitCase = LZ
boundLength VarCase = LS LZ
boundLength (TupleCase a b) = concatLength (boundLength a) (boundLength b)
boundLength (ConsCase vs) = LS (boundLength vs)
boundLength NilCase = LZ

assocLength :: Length bound -> Length xs -> proxy rest -> (((bound ++ xs) ++ rest) ~ (bound ++ (xs ++ rest)) => r) -> r
assocLength LZ _ _ ok = ok
assocLength (LS bs) xs p ok = assocLength bs xs p ok

-- | Increase all indices by 1 in an expression
shift :: forall x ys a. Exp ys a -> Exp (x ': ys) a
shift = go LZ
  where
    go :: forall xs b. Length xs -> Exp (xs ++ ys) b -> Exp (xs ++ x ': ys) b
    go len (Var i) = Var (shiftIndex len i)
    go len (Lam f) = Lam (go (LS len) f)
    go len (LamCase (pat :: Pattern bound c) (f :: Exp (bound ++ (xs ++ ys)) e)) =
      let blen = boundLength pat
       in assocLength blen len (Proxy :: Proxy ys) $
            assocLength blen len (Proxy :: Proxy (x ': ys)) $
              let h = go (concatLength blen len) f :: Exp ((bound ++ xs) ++ (x ': ys)) e
               in LamCase pat h
    go len (App f x) = App (go len f) (go len x)
    go len (At ix expr) = At ix (go len expr)
    go len (Construct xs) = Construct (fmap (go len) xs)
    go _ (Constant xs) = Constant xs
    go len (Tuple a b) = Tuple (go len a) (go len b)

    shiftIndex :: Length xs -> Index (xs ++ ys) b -> Index (xs ++ (x : ys)) b
    shiftIndex LZ i = IS i
    shiftIndex (LS _) IZ = IZ
    shiftIndex (LS len) (IS i) = IS (shiftIndex len i)

-- | Substitute the argument in the right-hand side expression with the
-- left-hand side expression.
substitute :: forall ys a b. Exp ys a -> Exp (a ': ys) b -> Exp ys b
substitute expr = go LZ
  where
    go :: forall xs c. Length xs -> Exp (xs ++ a ': ys) c -> Exp (xs ++ ys) c
    go len (Var index) = substituteIndex len index
    go len (Lam body) = Lam (go (LS len) body)
    go len (LamCase (pat :: Pattern bound x) (body :: Exp (bound ++ (xs ++ a ': ys)) d)) =
      let blen = boundLength pat
       in assocLength blen len (Proxy :: Proxy (a ': ys)) $
            assocLength blen len (Proxy :: Proxy ys) $
              let body' = go (concatLength (boundLength pat) len) body :: Exp ((bound ++ xs) ++ ys) d
               in LamCase pat body'
    go len (App f x) = App (go len f) (go len x)
    go len (At ix x) = At ix (go len x)
    go len (Construct xs) = Construct (fmap (go len) xs)
    go _ (Constant xs) = Constant xs
    go len (Tuple a b) = Tuple (go len a) (go len b)

    substituteIndex :: forall xs c. Length xs -> Index (xs ++ (a : ys)) c -> Exp (xs ++ ys) c
    substituteIndex LZ IZ = expr
    substituteIndex LZ (IS i) = Var i
    substituteIndex (LS _) IZ = Var IZ
    substituteIndex (LS len) (IS i) = shift (substituteIndex len i)

data Tensor f a = Tensor {tensorDims :: [Int], tensorData :: f a}

data Eval t where
  -- EvalFun' :: Exp '[a] b -> Eval (a -> b)
  EvalFun :: (Eval a -> Eval b) -> Eval (a -> b)
  Vec :: Vec n (Eval a) -> Eval (Vec n a)
  Pair :: Eval a -> Eval b -> Eval (a, b)
  -- | This case is here for the evaluated expressions to be useful
  EvalValue :: a -> Eval a

data List f xs where
  Nil' :: List f '[]
  Cons' :: f x -> List f xs -> List f (x ': xs)

concatList :: List f xs -> List f ys -> List f (xs ++ ys)
concatList Nil' ys = ys
concatList (Cons' x xs) ys = Cons' x (concatList xs ys)

bindVars :: Pattern bound a -> Eval a -> List Eval bound
bindVars UnitCase _ = Nil'
bindVars VarCase a = Cons' a Nil'
bindVars (TupleCase a b) (Pair x y) = concatList (bindVars a x) (bindVars b y)
bindVars (TupleCase a b) (EvalValue (x, y)) = concatList (bindVars a (EvalValue x)) (bindVars b (EvalValue y))
bindVars NilCase _ = Nil'
bindVars (ConsCase vs) (Vec (Cons a as)) = Cons' a (bindVars vs (Vec as))
bindVars (ConsCase vs) (EvalValue (Cons a as)) = Cons' (EvalValue a) (bindVars vs (EvalValue as))

eval :: List Eval ctx -> Exp ctx t -> Eval t
eval ctx (Var index) = lookupList index ctx
eval ctx (Lam expr) = EvalFun $ \a -> eval (Cons' a ctx) expr
eval ctx (LamCase pat expr) = EvalFun $ \a -> eval (concatList (bindVars pat a) ctx) expr
eval ctx (App f x) = appEval (eval ctx f) (eval ctx x)
eval ctx (At ix fs) = case eval ctx fs of
  Vec xs -> indexVec ix xs
  EvalValue xs -> EvalValue $ indexVec ix xs
eval ctx (Construct xs) = Vec $ fmap (eval ctx) xs
eval ctx (Tuple a b) = Pair (eval ctx a) (eval ctx b)
eval _ (Constant v) = EvalValue v

appEval :: Eval (a -> t) -> Eval a -> Eval t
appEval (EvalFun f) = f
appEval (EvalValue f) = EvalValue . f . uneval

uneval :: Eval a -> a
uneval (EvalValue a) = a
uneval (Pair a b) = (uneval a, uneval b)
uneval (EvalFun f) = uneval . f . EvalValue
uneval (Vec xs) = fmap uneval xs

lookupList :: Index ctx t -> List f ctx -> f t
lookupList IZ (Cons' x _) = x
lookupList (IS i) (Cons' _ xs) = lookupList i xs

sequence :: Exp ctx (a -> b) -> Exp ctx (b -> c) -> Exp ctx (a -> c)
sequence f g = Lam $ App (shift g) $ App (shift f) (Var IZ)

parallel :: Exp ctx (a -> b) -> Exp ctx (c -> d) -> Exp ctx ((a, c) -> (b, d))
parallel f g =
  LamCase (TupleCase VarCase VarCase) $
    let a = Var IZ
        c = Var (IS IZ)
        b = App (shift $ shift f) a
        d = App (shift $ shift g) c
     in Tuple b d

sequenceWeighted ::
  Exp ctx ((a, p) -> b) ->
  Exp ctx ((b, q) -> c) ->
  Exp ctx ((a, (p, q)) -> c)
sequenceWeighted f g =
  LamCase (TupleCase VarCase (TupleCase VarCase VarCase)) $
    let a = Var IZ
        p = Var (IS IZ)
        q = Var (IS (IS IZ))
        b = App (shift $ shift $ shift f) (Tuple a p)
        c = App (shift $ shift $ shift g) (Tuple b q)
     in c

data Nat = Zero | Succ Nat

data Vec n x where
  Nil :: Vec 'Zero x
  Cons :: x -> Vec n x -> Vec ('Succ n) x

type family (n :: Nat) + (m :: Nat) :: Nat where
  'Zero + m = m
  'Succ n + m = 'Succ (n + m)

class KnownNat n where
  knownNat :: Vec n ()

instance KnownNat 'Zero where
  knownNat = Nil

instance KnownNat n => KnownNat ('Succ n) where
  knownNat = Cons () knownNat

sequenceWeightedVec ::
  forall a b c p q x ctx.
  KnownNat p =>
  KnownNat q =>
  Exp ctx ((a, Vec p x) -> b) ->
  Exp ctx ((b, Vec q x) -> c) ->
  Exp ctx ((a, Vec (p + q) x) -> c)
sequenceWeightedVec f g =
  LamCase (TupleCase VarCase VarCase) $
    let a = Var IZ
        ws = Var (IS IZ)
        p = Construct (tabulate (\r -> At (leftRep knownNat knownNat r) ws))
        q = Construct (tabulate (\r -> At (rightRep knownNat knownNat r) ws))
        b = App (shift $ shift f) (Tuple a p)
        c = App (shift $ shift g) (Tuple b q)
     in c
  where
    leftRep :: Vec p () -> Vec q () -> Rep (Vec p) -> Rep (Vec (p + q))
    leftRep = go
      where
        go :: forall x y. Vec x () -> Vec y () -> Rep (Vec x) -> Rep (Vec (x + y))
        go _ _ FZ = FZ
        go (Cons _ xs) ys (FS i) = FS (go xs ys i)
    rightRep :: Vec p () -> Vec q () -> Rep (Vec q) -> Rep (Vec (p + q))
    rightRep = go
      where
        go :: forall x y. Vec x () -> Vec y () -> Rep (Vec y) -> Rep (Vec (x + y))
        go Nil _ i = i
        go (Cons _ xs) ys i = FS (go xs ys i)

parallelWeighted ::
  Exp ctx ((a, p) -> b) ->
  Exp ctx ((c, q) -> d) ->
  Exp ctx (((a, c), (p, q)) -> (b, d))
parallelWeighted f g =
  LamCase (TupleCase (TupleCase VarCase VarCase) (TupleCase VarCase VarCase)) $
    let a = Var IZ
        c = Var (IS IZ)
        p = Var (IS $ IS IZ)
        q = Var (IS $ IS $ IS IZ)
        b = App (shift $ shift $ shift $ shift f) (Tuple a p)
        d = App (shift $ shift $ shift $ shift g) (Tuple c q)
     in Tuple b d

data Length ctx where
  LZ :: Length '[]
  LS :: Length xs -> Length (x ': xs)

type family (xs :: [k]) ++ (ys :: [k]) :: [k] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

infixr 5 ++

class Functor f => Representable f where
  type Rep f :: Type
  tabulate :: (Rep f -> x) -> f x
  index :: Rep f -> f x -> x

data Fin n where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

instance Functor (Vec n) where
  fmap _ Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

indexVec :: Fin n -> Vec n a -> a
indexVec FZ (Cons x _) = x
indexVec (FS i) (Cons _ xs) = indexVec i xs

tabulateVec :: (Fin n -> x) -> Vec n a -> Vec n x
tabulateVec _ Nil = Nil
tabulateVec f (Cons _ xs) = Cons (f FZ) (tabulateVec (f . FS) xs)

instance KnownNat n => Representable (Vec n) where
  type Rep (Vec n) = Fin n
  index = indexVec
  tabulate f = tabulateVec f knownNat

instance Foldable (Vec n) where
  foldMap _ Nil = mempty
  foldMap f (Cons x xs) = f x <> foldMap f xs

instance Traversable (Vec n) where
  traverse _ Nil = pure Nil
  traverse f (Cons x xs) = Cons <$> f x <*> traverse f xs

-- Monadic evaluation

data MExp m ctx t where
  MVar :: Index ctx a -> MExp m ctx a
  MLam :: MExp m (a ': ctx) b -> MExp m ctx (a -> m b)
  MApp :: MExp m ctx (a -> m b) -> MExp m ctx a -> MExp m ctx b
  MAt :: Fin n -> MExp m ctx (Vec n a) -> MExp m ctx a
  MConstruct :: Vec n (MExp m ctx a) -> MExp m ctx (Vec n a)
  MFst :: MExp m ctx ((a, b) -> m a)
  MSnd :: MExp m ctx ((a, b) -> m b)
  MTuple :: MExp m ctx a -> MExp m ctx b -> MExp m ctx (a, b)
  MConstant :: a -> MExp m ctx a

data MEval m t where
  MEvalFun :: (MEval m a -> m (MEval m b)) -> MEval m (a -> m b)
  MVec :: Vec n (MEval m a) -> MEval m (Vec n a)
  MPair :: MEval m a -> MEval m b -> MEval m (a, b)
  MLift :: m (MEval m t) -> MEval m t
  MValue :: a -> MEval m a

evalM :: Monad m => List (MEval m) ctx -> MExp m ctx t -> MEval m t
evalM ctx (MVar i) = lookupList i ctx
evalM ctx (MLam expr) = MEvalFun $ \a -> pure $ evalM (Cons' a ctx) expr
evalM ctx (MApp a b) =
  let go :: Monad m => MEval m a -> MEval m (a -> m b) -> MEval m b
      go b' = \case
        MEvalFun f -> MLift $ f b'
        MLift f -> MLift $ fmap (go b') f
        MValue f -> MLift $ unevalM b' >>= fmap MValue . f
   in go (evalM ctx b) (evalM ctx a)
evalM ctx (MAt ix vec) =
  let go = \case
        MVec xs -> indexVec ix xs
        MLift as -> MLift $ fmap go as
        MValue xs -> MValue $ indexVec ix xs
   in go (evalM ctx vec)
evalM ctx (MConstruct xs) = MVec $ fmap (evalM ctx) xs
evalM _ MFst =
  MEvalFun $
    let go :: Monad m => MEval m (a, b) -> m (MEval m a)
        go = \case
          MPair a _ -> pure a
          MLift a -> a >>= go
          MValue a -> pure $ MValue $ fst a
     in go
evalM _ MSnd =
  MEvalFun $
    let go :: Monad m => MEval m (a, b) -> m (MEval m b)
        go = \case
          MPair _ b -> pure b
          MLift b -> b >>= go
          MValue b -> pure $ MValue $ snd b
     in go
evalM ctx (MTuple a b) = MPair (evalM ctx a) (evalM ctx b)
evalM _ (MConstant c) = MValue c

unevalM :: Monad m => MEval m t -> m t
unevalM (MEvalFun f) = pure $ \a -> f (MValue a) >>= unevalM
unevalM (MVec xs) = traverse unevalM xs
unevalM (MPair a b) = liftA2 (,) (unevalM a) (unevalM b)
unevalM (MValue a) = pure a
unevalM (MLift x) = x >>= unevalM
