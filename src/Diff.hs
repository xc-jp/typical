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

data a :-> b where
  D :: Tangent x tx -> Arr tx a b -> a :-> b

-- Correlate a point with its tangent
-- This is needed for the Arrow case to ensure
-- that the tangent tx is corresponding to the exponential (a :-> b)
-- and not just existentially quantified inside (a :-> b)
data Point a ta where
  Arrow :: Tangent x tx -> Arr tx a b -> Point (a :-> b) tx
  Point :: a -> Tangent a ta -> Point a ta
  PointTuple :: Point a ta -> Point b tb -> Point (a, b) (ta, tb)

-- Can not contain arrows because then we need the slow curry implementation
data Tangent a ta where
  TanFloat :: Tangent (Sum Float) (Sum Float)
  TanTuple ::
    Tangent a ta ->
    Tangent b tb ->
    Tangent (a, b) (ta, tb)
  TanUnit :: Tangent () ()
  TanInt :: Tangent Int ()
  TanBool :: Tangent Bool ()

deriving instance Show (Tangent a ta)

-- | Arrows are not points
arrow :: Point (a :-> b) tx -> (forall x. Tangent x tx -> Arr tx a b -> r) -> r
arrow (Point _ t) _ = case t of
arrow (Arrow x f) k = k x f

idD :: a :-> a
idD = D TanUnit $ \p k -> k p ((),)

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
  D (TanTuple ttx tty) $ \pac k ->
    untuplePoint pac $ \(pa, pc) ->
      let kf = f pa
          kg = g pc
       in kf $ \pb f' ->
            kg $ \pd g' ->
              k (PointTuple pb pd) $ \(tb, td) ->
                let (xf, ta) = f' tb
                    (xg, tc) = g' td
                 in ((xf, xg), (ta, tc))

fstD :: (a, b) :-> a
fstD = D TanUnit $ \pab k -> untuplePoint pab $ \(pa, pb) ->
  pointTangent pb $ \tb -> monoidTangent tb $ k pa (\ta -> ((), (ta, mempty)))

sndD :: (a, b) :-> b
sndD = D TanUnit $ \pab k -> untuplePoint pab $ \(pa, pb) ->
  pointTangent pa $ \ta -> monoidTangent ta $ k pb (\tb -> ((), (mempty, tb)))

dupD :: a :-> (a, a)
dupD = D TanUnit $ \pa k ->
  pointTangent pa $ \tta ->
    monoidTangent tta $ k (PointTuple pa pa) (\(ta, tb) -> ((), ta <> tb))

curryD ::
  forall a b c.
  (a, b) :-> c ->
  a :-> (b :-> c)
curryD (D (x :: Tangent x tx) f) = D x h
  where
    -- Arr tx a (b :-> c)
    -- But I need ta in scope for g to have a type signature
    h ::
      forall ta.
      Point a ta ->
      ( forall r.
        (forall tb. Point (b :-> c) tb -> (tb -> (tx, ta)) -> r) ->
        r
      )
    h pa k = pointTangent pa $ \tta -> k (Arrow (TanTuple x tta) g) id
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
uncurryD (D _ f) = D TanUnit $ \pab k ->
  untuplePoint pab $ \(pa, pb) ->
    let kf = f pa
     in kf $ \arrg f' ->
          arrow arrg $ \_ g ->
            let kg = g pb
             in kg $ \pc g' ->
                  k pc $ \tc ->
                    let (ty, tb) = g' tc
                        (_, ta) = f' ty
                     in ((), (ta, tb))

applyD :: (a :-> b, a) :-> b
applyD = D TanUnit $ \pfa k ->
  untuplePoint pfa $ \(pf, pa) ->
    arrow pf $ \_ f ->
      let kf = f pa
       in kf $ \b f' ->
            k b (\tc -> ((), f' tc))

untuplePoint :: Point (a, c) t -> (forall ta tc. t ~ (ta, tc) => (Point a ta, Point c tc) -> r) -> r
untuplePoint (PointTuple a b) r = r (a, b)
untuplePoint (Point (a, b) (TanTuple ta tb)) r = r (Point a ta, Point b tb)

-- Simplify converting simple functions (a -> b) to (a :-> b)
class KnownTangent a where
  type Tan a
  knownTangent :: Tangent a (Tan a)
  tangent :: Tangent a ta -> (ta ~ Tan a => r) -> r
  pointTangent' :: Point a ta -> Tangent a ta

instance KnownTangent (Sum Float) where
  type Tan (Sum Float) = Sum Float
  knownTangent = TanFloat
  tangent TanFloat r = r
  pointTangent' (Point _ ta) = ta

instance KnownTangent Int where
  type Tan Int = ()
  knownTangent = TanInt
  tangent TanInt r = r
  pointTangent' (Point _ ta) = ta

instance KnownTangent Bool where
  type Tan Bool = ()
  knownTangent = TanBool
  tangent TanBool r = r
  pointTangent' (Point _ ta) = ta

instance KnownTangent () where
  type Tan () = ()
  knownTangent = TanUnit
  tangent TanUnit r = r
  pointTangent' (Point _ ta) = ta

instance (KnownTangent a, KnownTangent b) => KnownTangent (a, b) where
  type Tan (a, b) = (Tan a, Tan b)
  knownTangent = TanTuple knownTangent knownTangent
  tangent (TanTuple a b) r = tangent a $ tangent b r
  pointTangent' (Point _ ta) = ta
  pointTangent' (PointTuple pa pb) = TanTuple (pointTangent' pa) (pointTangent' pb)

node :: forall a b. (KnownTangent a, KnownTangent b) => (a -> (b, Tan b -> Tan a)) -> a :-> b
node f = D TanUnit $ \(pa :: Point a ta) k ->
  tangent (pointTangent' pa) $
    let (b, f') = f (pointValue pa)
     in k (Point b knownTangent) (\tb -> ((), f' tb))

multiply :: (Sum Float, Sum Float) :-> Sum Float
multiply = node $ \(a, b) -> (a * b, \tc -> (tc * b, tc * a))

add :: (Sum Float, Sum Float) :-> Sum Float
add = node $ \(a, b) -> (a <> b, \tc -> (tc, tc))

equalTangent :: Tangent a ta -> Tangent a tx -> (ta ~ tx => r) -> r
equalTangent TanFloat TanFloat r = r
equalTangent (TanTuple a b) (TanTuple c d) r = equalTangent a c $ equalTangent b d r
equalTangent TanUnit TanUnit r = r
equalTangent TanInt TanInt r = r
equalTangent TanBool TanBool r = r

monoidTangent :: Tangent a ta -> (Monoid ta => r) -> r
monoidTangent TanFloat r = r
monoidTangent (TanTuple a b) r = monoidTangent a $ monoidTangent b r
monoidTangent TanUnit r = r
monoidTangent TanInt r = r
monoidTangent TanBool r = r

pointTangent :: Point a ta -> (forall b. Tangent b ta -> r) -> r
pointTangent (Point _ ta) k = k ta
pointTangent (Arrow ta _) k = k ta
pointTangent (PointTuple pa pb) k = pointTangent pa $ \ta -> pointTangent pb $ \tb -> k (TanTuple ta tb)

pointValue :: Point a ta -> a
pointValue (Point a _) = a
pointValue (Arrow x f) = D x f
pointValue (PointTuple a b) = (pointValue a, pointValue b)
