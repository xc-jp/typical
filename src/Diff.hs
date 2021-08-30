{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Diff where

import Data.Monoid (Sum)

-- Differentable function from a to b with some extra hidden state tx for the
-- backprop
type Arr tx a b =
  ( forall ta.
    Point a ta ->
    ( forall r.
      (forall tb. Point b tb -> (tb -> (tx, ta)) -> r) ->
      r
    )
  )

-- | Types of valid tangents
data Tan a where
  TanFloat :: Tan (Sum Float)
  TanTuple :: Tan a -> Tan b -> Tan (a, b)
  TanUnit :: Tan ()
  TanNil :: Tan (List '[])
  TanCons :: Tan x -> Tan (List xs) -> Tan (List (x ': xs))

deriving instance Show (Tan ta)

data a :-> b where
  D :: Tan tx -> Arr tx a b -> a :-> b

-- | Valid values (points) with their respective tangent types We require all
-- tangents to be additive monoids. Without this constraint the backpropagation
-- doesn't make sense. However, this makes it unclear what to do with types
-- like Tensor Float. If we know the exact dimensions then there's a monoid for
-- Tensor dims Float, but otherwise mempty is not defined.
data Point a ta where
  Arrow :: Tan tx -> Arr tx a b -> Point (a :-> b) tx
  PointFloat :: Sum Float -> Point (Sum Float) (Sum Float)
  PointTuple :: Point a ta -> Point b tb -> Point (a, b) (ta, tb)
  PointUnit :: Point () ()
  PointInt :: Int -> Point Int ()
  PointBool :: Bool -> Point Bool ()
  PointNil :: Point (List '[]) (List '[])
  PointCons :: Point x t -> Point (List xs) (List ts) -> Point (List (x ': xs)) (List (t ': ts))
  PointIZ :: Point (Index (x ': xs) x) ()
  PointIS :: Point (Index xs x) () -> Point (Index (y ': xs) x) ()

instance Show (Point a ta) where
  show (Arrow t _) = "<<arr>> : " <> show t
  show (PointFloat x) = show x
  show (PointTuple a b) = show (a, b)
  show PointUnit = "unit"
  show (PointInt x) = show x
  show (PointBool x) = show x
  show PointNil = "[]"
  show (PointCons x xs) = show x <> " :: " <> show xs
  show PointIZ = "[0]"
  show (PointIS i) = "[" <> show (succ (ix i)) <> "]"
    where
      ix :: Point (Index xs x) () -> Int
      ix PointIZ = 0
      ix (PointIS n) = succ (ix n)

monoidTangent :: Point a ta -> (Monoid ta => r) -> r
monoidTangent (Arrow x _) r = monoidTan x r
monoidTangent (PointFloat _) r = r
monoidTangent (PointTuple a b) r = monoidTangent a $ monoidTangent b r
monoidTangent PointUnit r = r
monoidTangent (PointInt _) r = r
monoidTangent (PointBool _) r = r
monoidTangent PointNil r = r
monoidTangent (PointCons t ts) r = monoidTangent t $ monoidTangent ts r
monoidTangent PointIZ r = r
monoidTangent (PointIS _) r = r

monoidTan :: Tan a -> (Monoid a => r) -> r
monoidTan TanFloat r = r
monoidTan (TanTuple a b) r = monoidTan a $ monoidTan b r
monoidTan TanUnit r = r
monoidTan TanNil r = r
monoidTan (TanCons x xs) r = monoidTan x $ monoidTan xs r

pointTangent :: Point a ta -> Tan ta
pointTangent (Arrow x _) = x
pointTangent (PointTuple a b) = TanTuple (pointTangent a) (pointTangent b)
pointTangent PointFloat {} = TanFloat
pointTangent PointUnit {} = TanUnit
pointTangent PointInt {} = TanUnit
pointTangent PointBool {} = TanUnit
pointTangent PointNil {} = TanNil
pointTangent (PointCons x xs) = TanCons (pointTangent x) (pointTangent xs)
pointTangent PointIZ = TanUnit
pointTangent PointIS {} = TanUnit

data Index xs t where
  IZ :: Index (t ': xs) t
  IS :: Index xs t -> Index (y ': xs) t

data List xs where
  Nil :: List '[]
  Cons :: x -> List xs -> List (x ': xs)

instance Semigroup (List '[]) where
  _ <> _ = Nil

instance (Semigroup t, Semigroup (List ts)) => Semigroup (List (t ': ts)) where
  Cons x xs <> Cons y ys = Cons (x <> y) (xs <> ys)

instance Monoid (List '[]) where
  mempty = Nil

instance (Monoid t, Monoid (List ts)) => Monoid (List (t ': ts)) where
  mempty = Cons mempty mempty

--- Combinator library for differentiable arrows a :-> b
idD :: a :-> a
idD = D TanUnit $ \p k -> k p ((),)

constD :: Point b tb -> (a :-> b)
constD b = D TanUnit $ \pa k ->
  monoidTangent pa $
    k b (const ((), mempty))

sequenceD ::
  (a :-> b) ->
  (b :-> c) ->
  (a :-> c)
sequenceD (D txf f) (D txg g) = D (TanTuple txf txg) $ \pa k ->
  let kf = f pa
   in kf $ \pb f' ->
        let kg = g pb
         in kg $ \pc g' ->
              k pc $ \tc ->
                let (xg, tb) = g' tc
                    (xf, ta) = f' tb
                 in ((xf, xg), ta)

parallelD :: a :-> b -> c :-> d -> (a, c) :-> (b, d)
parallelD (D ttx f) (D tty g) =
  D (TanTuple ttx tty) $ \(PointTuple pa pc) k ->
    let kf = f pa
        kg = g pc
     in kf $ \pb f' ->
          kg $ \pd g' ->
            k (PointTuple pb pd) $ \(tb, td) ->
              let (xf, ta) = f' tb
                  (xg, tc) = g' td
               in ((xf, xg), (ta, tc))

fanOutD :: a :-> b -> a :-> c -> a :-> (b, c)
fanOutD f g = sequenceD dupD (parallelD f g)

-- diff :: Ctx a -> Lam b -> a :-> b
-- diff ctx (App f x) = sequenceD (fanOutD (diff ctx f) (diff ctx x)) applyD

fstD :: (a, b) :-> a
fstD = D TanUnit $ \(PointTuple pa pb) k -> monoidTangent pb $ k pa (\ta -> ((), (ta, mempty)))

sndD :: (a, b) :-> b
sndD = D TanUnit $ \(PointTuple pa pb) k -> monoidTangent pa $ k pb (\tb -> ((), (mempty, tb)))

dupD :: a :-> (a, a)
dupD = D TanUnit $ \pa k -> monoidTangent pa $ k (PointTuple pa pa) (\(ta, tb) -> ((), ta <> tb))

curryD ::
  forall a b c.
  (a, b) :-> c ->
  a :-> (b :-> c)
curryD (D (x :: Tan tx) f) = D x h
  where
    -- Arr tx a (b :-> c) expanded
    -- But I need ta in scope for g to have a type signature
    h ::
      forall ta.
      Point a ta ->
      ( forall r.
        (forall tb. Point (b :-> c) tb -> (tb -> (tx, ta)) -> r) ->
        r
      )
    h pa k = k (Arrow (TanTuple x (pointTangent pa)) g) id
      where
        -- g also backprops ta in the hidden state
        g :: Arr (tx, ta) b c
        g pb k' =
          let kf = f (PointTuple pa pb)
           in kf $ \pc f' ->
                k' pc $ \tc ->
                  let (tx, (ta, tb)) = f' tc
                   in ((tx, ta), tb)

uncurryD :: (a :-> (b :-> c)) -> (a, b) :-> c
uncurryD (D x f) = D x $ \(PointTuple pa pb) k ->
  let kf = f pa
   in kf $ \(Arrow _ g) f' ->
        let kg = g pb
         in kg $ \pc g' ->
              k pc $ \tc ->
                -- the tangent of (b :-> c) is ty, which is passed to f'
                let (ty, tb) = g' tc
                    (tx, ta) = f' ty
                 in (tx, (ta, tb))

applyD :: (a :-> b, a) :-> b
applyD = D TanUnit $ \(PointTuple (Arrow _ f) pa) k ->
  let kf = f pa
   in kf $ \b f' ->
        k b (\tc -> ((), f' tc))

atD :: Index xs x -> List xs :-> x
atD i = D TanUnit $ \xs k -> at i xs $ \j p -> k p (\t -> ((), backpropAt j xs t))

at :: Index xs x -> Point (List xs) tl -> (forall ts t. (tl ~ List ts) => Index ts t -> Point x t -> r) -> r
at IZ (PointCons t _) k = k IZ t
at (IS i) (PointCons _ xs) k = at i xs $ \j t -> k (IS j) t

backpropAt :: Index ts t -> Point (List xs) (List ts) -> t -> List ts
backpropAt IZ (PointCons _ tail') t = monoidTangent tail' $ Cons t mempty
backpropAt (IS i) (PointCons head' ts) t = monoidTangent head' $ Cons mempty (backpropAt i ts t)

--- End of combinators

-- | Simplify construction of primitive functions
class KnownPoint a where
  type Tangent a
  knownPoint :: a -> Point a (Tangent a)
  uniquePoint :: Point a ta -> (ta ~ Tangent a => r) -> r

instance KnownPoint (Sum Float) where
  type Tangent (Sum Float) = Sum Float
  knownPoint = PointFloat
  uniquePoint (PointFloat _) r = r

instance KnownPoint Int where
  type Tangent Int = ()
  knownPoint = PointInt
  uniquePoint (PointInt _) r = r

instance KnownPoint Bool where
  type Tangent Bool = ()
  knownPoint = PointBool
  uniquePoint (PointBool _) r = r

instance KnownPoint () where
  type Tangent () = ()
  knownPoint _ = PointUnit
  uniquePoint PointUnit r = r

instance (KnownPoint a, KnownPoint b) => KnownPoint (a, b) where
  type Tangent (a, b) = (Tangent a, Tangent b)
  knownPoint (a, b) = PointTuple (knownPoint a) (knownPoint b)
  uniquePoint (PointTuple a b) r = uniquePoint a $ uniquePoint b r

-- | Lift a function (a -> (b, Tangent b -> Tangent a)) into a differentiable
-- function a :-> b given that we know what the tangents for a and b are.
prim :: forall a b. (KnownPoint a, KnownPoint b) => (a -> (b, Tangent b -> Tangent a)) -> a :-> b
prim f = D TanUnit $ \pa k ->
  uniquePoint pa $
    let (b, f') = f (pointValue pa)
     in k (knownPoint b) (\tb -> ((), f' tb))

multiply :: (Sum Float, Sum Float) :-> Sum Float
multiply = prim $ \(a, b) -> (a * b, \tc -> (tc * b, tc * a))

add :: (Sum Float, Sum Float) :-> Sum Float
add = prim $ \(a, b) -> (a <> b, \tc -> (tc, tc))

pointValue :: Point a ta -> a
pointValue (Arrow x f) = D x f
pointValue (PointTuple a b) = (pointValue a, pointValue b)
pointValue PointIZ = IZ
pointValue (PointIS p) = IS (pointValue p)
pointValue (PointFloat x) = x
pointValue (PointInt x) = x
pointValue (PointBool x) = x
pointValue PointUnit = ()
pointValue PointNil = Nil
pointValue (PointCons x xs) = Cons (pointValue x) (pointValue xs)
