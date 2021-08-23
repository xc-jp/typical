{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}

module Lib where

import Data.Functor.Identity
import Data.Kind
import Numeric.Natural (Natural)
import Rebound

type Ty = TyF Identity

newtype TyDim = Dim Natural

type TyDims f = TyList TyDim f

data TyElt = EltFloat

data TyF (f :: Type -> Type)
  = TyList (TyList (TyF f) f)
  | TyTensor (TyDims f) (f TyElt)
  | TyArr (TyF f) (TyF f)

data TyList a f
  = TyCons (f a) (f (TyList a f))
  | TyNil

data Pattern
  = NilCase
  | ConsCase Pattern Pattern
  | VarCase

data Prim = Mult

data ConstructorF f
  = CCons f f
  | CNil

data Pattern' c
  = PBind
  | PIgnore
  | PConstructor (c (Pattern' c))

data Typ tcons t
  = TypVar t
  | TypForall (Typ tcons (Bind () t))
  | TypArr (Typ tcons t) (Typ tcons t)
  | TypCons (tcons (Typ tcons t))
  deriving (Functor, Foldable, Traversable)

data Exp tcons cons t v
  = Lam (Pattern' cons) (Typ tcons t) (Exp tcons cons t (Bind Natural v))
  | Var v
  | App (Exp tcons cons t v) (Exp tcons cons t v)
  | Cons (cons (Exp tcons cons t v))
  | TLam (Exp tcons cons (Bind () t) v)
  | TApp (Exp tcons cons t v) (Typ tcons t)
  deriving (Functor, Foldable, Traversable)

exprTraversal ::
  forall m t t' v v' c tc.
  (Applicative m, Traversable c, Traversable tc) =>
  (t -> m t') ->
  (v -> m v') ->
  (Exp tc c t v -> m (Exp tc c t' v'))
exprTraversal ft fv = go
  where
    go (Lam pat typ body) = Lam pat <$> traverse ft typ <*> exprTraversal ft (traverse fv) body
    go (Var v) = Var <$> fv v
    go (App f x) = App <$> go f <*> go x
    go (Cons c) = Cons <$> traverse go c
    go (TApp f t) = TApp <$> go f <*> traverse ft t
    go (TLam body) = TLam <$> exprTraversal (traverse ft) fv body
