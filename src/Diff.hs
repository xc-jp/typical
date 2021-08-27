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
import Data.Type.Equality (type (:~:) (Refl))

-- type Diff a b = Diff' a b (Tangent a) (Tangent b)

{-
vjp :: Diff a b -> a -> (Tangent b -> Tangent a)
vjp (Diff f) x = snd (f x)
-}

-- Slow curry calling f for each gradient in the tangent space
{-
curryDiff ::
  forall a b c ta tb tc.
  Monoid ta =>
  Diff' (a, b) c (ta, tb) tc ->
  Diff' a (Diff' b c tb tc) ta [(b, tc)]
curryDiff (Diff f) = Diff new_f
  where
    new_f a = (Diff new_g, h)
      where
        new_g :: b -> (c, tc -> tb)
        new_g b = let (c, f') = f (a, b) in (c, snd . f')
        h :: [(b, tc)] -> ta
        h grads = foldl' (<>) mempty (map reach grads)
          where
            reach (b, grad) = fst (snd (f (a, b)) grad)

curryDiff' ::
  forall a b c ta tb tc.
  Monoid ta =>
  Diff' (a, b) c (ta, tb) tc ->
  Diff' a (Diff' b c tb tc) ta [(b, tc)]
curryDiff' (Diff f) = Diff new_f
  where
    new_f a = (Diff new_g, h)
      where
        new_g :: b -> (c, tc -> tb)
        new_g b = let (c, f') = f (a, b) in (c, snd . f')
        h :: [(b, tc)] -> ta
        h grads = foldl' (<>) mempty (map reach grads)
          where
            reach (b, grad) = fst (snd (f (a, b)) grad)
-}

{-
curryDiff2 ::
  forall a b c ta tb tc.
  Monoid ta =>
  Diff' (a, b) c (ta, tb) tc ->
  Diff' a (Diff' b c tb tc) ta [(b, tc)]
curryDiff2 (Diff f) = Diff new_f
  where
    new_f :: a -> (Diff' b c tb tc, [(b, tc)] -> ta)
    new_f a = (Diff g, new_pb)
      where
        gf :: b -> (c, tc -> tb)
        gf b =
          let (c, pb) = f (a, b)
           in ( c,
                \tc ->
                  let (cte, (ctt, cts)) = pb tc
                   in ((cte, ctt), cts)
              )
        g :: b -> (c, tc -> tb)
        g = gf

        new_pb :: [(b, tc)] -> ta
        new_pb env = env
  -}

data a :-> b where
  D ::
    Tangent x tx ->
    ( forall ta.
      a ->
      Tangent a ta ->
      ( forall r.
        (forall tb. Tangent b tb -> (b, tb -> (tx, ta)) -> r) ->
        r
      )
    ) ->
    a :-> b

class KnownTangent a where
  type Tan a
  knownTangent :: Tangent a (Tan a)
  tangent :: Tangent a ta -> (ta ~ Tan a => r) -> r

instance KnownTangent (Sum Float) where
  type Tan (Sum Float) = Sum Float
  knownTangent = TanFloat
  tangent TanFloat r = r

instance KnownTangent Int where
  type Tan Int = ()
  knownTangent = TanInt
  tangent TanInt r = r

instance KnownTangent Bool where
  type Tan Bool = ()
  knownTangent = TanBool
  tangent TanBool r = r

instance KnownTangent () where
  type Tan () = ()
  knownTangent = TanUnit
  tangent TanUnit r = r

instance (KnownTangent a, KnownTangent b) => KnownTangent (a, b) where
  type Tan (a, b) = (Tan a, Tan b)
  knownTangent = TanTuple knownTangent knownTangent
  tangent (TanTuple a b) r = tangent a $ tangent b r

data Tangent a ta where
  TanDiff :: Tangent x tx -> Tangent (a :-> b) tx
  TanFloat :: Tangent (Sum Float) (Sum Float)
  TanTuple ::
    Tangent a ta ->
    Tangent b tb ->
    Tangent (a, b) (ta, tb)
  TanUnit :: Tangent () ()
  TanInt :: Tangent Int ()
  TanBool :: Tangent Bool ()

deriving instance Show (Tangent a ta)

monoidTangent :: Tangent a ta -> (Monoid ta => r) -> r
monoidTangent TanFloat r = r
monoidTangent (TanDiff x) r = monoidTangent x r
monoidTangent (TanTuple a b) r = monoidTangent a $ monoidTangent b r
monoidTangent TanUnit r = r
monoidTangent TanInt r = r
monoidTangent TanBool r = r

node :: (KnownTangent a, KnownTangent b) => (a -> (b, Tan b -> Tan a)) -> a :-> b
node f = D TanUnit $ \a tta k ->
  tangent tta $
    let (b, f') = f a
     in k knownTangent (b, \tb -> ((), f' tb))

node' :: Tangent b tb -> (forall ta. Tangent a ta -> a -> (b, tb -> ta)) -> a :-> b
node' ttb f = D TanUnit $ \a tta k ->
  let (b, f') = f tta a
   in k ttb (b, \tb -> ((), f' tb))

curryD ::
  forall a b c.
  (a, b) :-> c ->
  a :-> (b :-> c)
curryD (D (x :: Tangent x tx) f) =
  D x new_f
  where
    new_f ::
      forall ta.
      a ->
      Tangent a ta ->
      ( forall r.
        (forall tb. Tangent (b :-> c) tb -> (b :-> c, tb -> (tx, ta)) -> r) ->
        r
      )
    new_f a tta k = k (TanDiff (TanTuple x tta)) (D (TanTuple x tta) g, id)
      where
        g ::
          forall tb.
          b ->
          Tangent b tb ->
          ( forall r'.
            (forall tc. Tangent c tc -> (c, tc -> ((tx, ta), tb)) -> r') ->
            r'
          )
        g b ttb k' =
          let l = f (a, b) (TanTuple tta ttb)
           in l $ \ttc -> reassoc $ k' ttc
          where
            reassoc m (c, n) = m (c, \tc -> let (tx, (ta, tb)) = n tc in ((tx, ta), tb))

uncurry :: (a -> (b -> c)) -> (a, b) -> c
uncurry f (a, b) = f a b

uncurryD :: (a :-> (b :-> c)) -> (a, b) :-> c
uncurryD (D _ f) = D TanUnit $ \(a, b) (TanTuple tta ttb) k ->
  let kf = f a tta
   in kf $ \ttb' (D y g, f') ->
        let kg = g b ttb
         in kg $ \ttc' (c, g') ->
              k
                ttc'
                ( c,
                  \tc ->
                    case equalTangents ttb' y of
                      Just Refl ->
                        let (ty, tb) = g' tc
                            (_, ta) = f' ty
                         in ((), (ta, tb))
                      Nothing -> error $ "Internal error: " <> show y <> " does not match passed " <> show ttb'
                )

-- It is very unfortunate this did not just work out
applyD :: (a :-> b, a) :-> b
applyD = D TanUnit $ \(D x f, a) (TanTuple (TanDiff ttf) tta) k ->
  case equalTangents x ttf of
    Just Refl ->
      let kf = f a tta
       in kf $ \ttb (b, f') ->
            k ttb $
              tuple b $ \tb ->
                ((), f' tb)
    Nothing -> error $ "Internal error: " <> show x <> " does not match passed " <> show ttf

equalTangents :: Tangent x tx -> Tangent y ty -> Maybe (tx :~: ty)
equalTangents TanFloat TanFloat = Just Refl
equalTangents TanFloat _ = Nothing
equalTangents (TanDiff x) y = equalTangents x y
equalTangents x (TanDiff y) = equalTangents x y
equalTangents (TanTuple a b) (TanTuple c d) = do
  Refl <- equalTangents a c
  Refl <- equalTangents b d
  pure Refl
equalTangents (TanTuple _ _) _ = Nothing
equalTangents x y = do
  Refl <- unitTangent x
  Refl <- unitTangent y
  pure Refl
  where
    unitTangent :: Tangent a ta -> Maybe (ta :~: ())
    unitTangent TanFloat = Nothing
    unitTangent (TanTuple _ _) = Nothing
    unitTangent (TanDiff a) = unitTangent a
    unitTangent TanUnit = Just Refl
    unitTangent TanBool = Just Refl
    unitTangent TanInt = Just Refl

idD :: a :-> a
idD = D TanUnit $ \a tta k -> k tta (a, tuple ())

sequenceD ::
  (a :-> b) ->
  (b :-> c) ->
  (a :-> c)
sequenceD (D txf f) (D txg g) = D (TanTuple txf txg) $ \a tta k ->
  let kf = f a tta
   in kf $ \ttb (b, f') ->
        let kg = g b ttb
         in kg $ \ttc (c, g') ->
              k ttc $
                tuple c $ \tc ->
                  let (xg, tb) = g' tc
                      (xf, ta) = f' tb
                   in ((xf, xg), ta)

parallelD :: a :-> b -> c :-> d -> (a, c) :-> (b, d)
parallelD (D ttx f) (D tty g) =
  D (TanTuple ttx tty) $ \(a, c) (TanTuple tta ttc) k ->
    let kf = f a tta
        kg = g c ttc
     in kf $ \ttb (b, f') ->
          kg $ \ttd (d, g') ->
            k (TanTuple ttb ttd) $
              tuple (b, d) $ \(tb, td) ->
                let (xf, ta) = f' tb
                    (xg, tc) = g' td
                 in ((xf, xg), (ta, tc))

tuple :: a -> b -> (a, b)
tuple a b = (a, b)

vjp' ::
  a :-> b ->
  Tangent a ta ->
  a ->
  ( forall r.
    ( forall tb. Tangent b tb -> (tb -> ta) -> r
    ) ->
    r
  )
vjp' (D _ f) tta x g =
  let k = f x tta
   in k $ \ttb (_, f') ->
        g ttb $ \tb -> snd $ f' tb

vjp :: (KnownTangent a, KnownTangent b) => (a :-> b) -> a -> Tan b -> Tan a
vjp d x = vjp' d knownTangent x $ \ttb g -> tangent ttb g

-- id_a where a is determined by the Tangent witness

{-

parallelDiff :: Diff a b -> Diff c d -> Diff (a, c) (b, d)
parallelDiff (Diff f) (Diff g) = Diff $ \(a, c) ->
  let (b, f') = f a
      (d, g') = g c
   in ((b, d), bimap f' g')

sequenceDiff :: Diff a b -> Diff b c -> Diff a c
sequenceDiff (Diff f) (Diff g) = Diff $ \a ->
  let (b, f') = f a
      (c, g') = g b
   in (c, f' . g')
-}

{-
-}

{-
let (c, g') = _ f
 in ( c,
      \tc ->
        let (tx, (ta, tb)) = g'
         in ((tx, ta), tb)
    )
-}

{-
-}

{-
curryDiff2 :: forall a b c. Diff2 (a, b) c -> Diff2 a (Diff b c)
curryDiff2 (Diff2 (TanDiff tx tc) f) =
  Diff2 (_ tx tc) _
  where
    new_f ::
      Tangent' a ta ->
      Tangent' b tb ->
      Tangent' c tc ->
      a ->
      (Diff' b c tb tc, [(b, tc)] -> (x, ta))
    new_f ta' tb' tc' a = (Diff gf, _)
      where
        gf :: b -> (c, tc -> ((x, ta), tb))
        gf = undefined

    g :: Differ b c (Tangent b) tc
    g = error "not implemented"

    g' :: [(b, tc)] -> Tangent a
    g' = error "not implemented"
    -}

{-
     curry :: ((τt,τs)  τr) →(τt  (τs  τr))
curry (exT τ[ f) = exT () new_f
where
new_f :: Π(t:τt). Σ(g : τs  τr). T[g] →(τ[, T[t])
new_f t =
let gf :: Π(s:τs).Σ(r:τr). T[r] →((τ[,T[t]), T[s])
gf s = let (r, pullback) = f(t,s)
in (r, λgr →
let (cte,(ctt,cts)) = pullback gr
in (( cte,ctt), cts))
g = exT (τ[,T[t]) gf
new_pb :: T[g] →(τ[,T[t])
new_pb env = env
in (g, new_pb
-}

{-
uncurryDiff :: forall a b c. Diff a (Diff b c) -> Diff (a, b) c
uncurryDiff f = sequenceDiff (parallelDiff f idDiff) applyDiff

idDiff :: Diff a a
idDiff = Diff (,id)

applyDiff :: Diff (Diff a b, a) b
applyDiff = Diff $ \(Diff f, x) ->
  let (b, f') = f x
   in (b, \db -> ([(x, db)], f' db))

parallelDiff :: Diff a b -> Diff c d -> Diff (a, c) (b, d)
parallelDiff (Diff f) (Diff g) = Diff $ \(a, c) ->
  let (b, f') = f a
      (d, g') = g c
   in ((b, d), bimap f' g')

sequenceDiff :: Diff a b -> Diff b c -> Diff a c
sequenceDiff (Diff f) (Diff g) = Diff $ \a ->
  let (b, f') = f a
      (c, g') = g b
   in (c, f' . g')

multiply :: Diff (Float, Float) Float
multiply = Diff $ \(a, b) -> (a * b, \dc -> (dc * b, dc * a))

add :: Monoid a => Diff' (a, a) a (ta, ta) ta
add = Diff $ \(a, b) -> (a <> b, \dc -> (dc, dc))

fstDiff :: Monoid tb => Diff' (a, b) a (ta, tb) ta
fstDiff = Diff $ \(a, _) -> (a, (,mempty))

sndDiff :: Monoid ta => Diff' (a, b) b (ta, tb) tb
sndDiff = Diff $ \(_, b) -> (b, (mempty,))

dupDiff :: Monoid ta => Diff' a (a, a) ta (ta, ta)
dupDiff = Diff $ \a -> ((a, a), uncurry (<>))
-}
