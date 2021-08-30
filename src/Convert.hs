{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Convert where

import Data.Void (Void)

data Prim = Fst | Snd | Add | Mul
  deriving (Show)

data Type
  = TFloat
  | TTuple Type Type
  | TArr Type Type
  | TUnit
  deriving (Show)

data Exp v
  = Lam (Exp (Maybe v))
  | Var v
  | App (Exp v) (Exp v)
  | Tuple (Exp v) (Exp v)
  | Unit
  | Const Float
  | Zero (Exp v)
  | Type Type
  | Primitive Prim
  deriving (Functor, Foldable, Traversable, Show)

data Value
  = Closure (Value -> Value)
  | Pair Value Value
  | Number Float
  | UnitValue
  | TypeValue Type

data Context v where
  EmptyCtx :: Context Void
  Bind :: Context v -> Context (Maybe v)

convert :: Context v -> Exp v -> Exp o
convert ctx (Lam e) = curryD $ convert (Bind ctx) e
convert ctx (Var i) = convertVar ctx i
convert ctx (App f x) = (convert ctx f `fanOut` convert ctx x) `sequenceD` applyD
convert ctx (Tuple a b) = convert ctx a `fanOut` convert ctx b
convert _ (Zero _) = error "Cannot differentiate zero (yet?)"
convert _ Unit = constD Unit
convert _ (Const x) = constD (Const x)
convert _ (Primitive Fst) = fstD
convert _ (Primitive Snd) = sndD
convert _ (Primitive Add) = addD
convert _ (Primitive Mul) = mulD
convert _ (Type _) = error "Cannot convert type"

data Ctx v where
  EmptyCtx' :: Ctx Void
  Bind' :: Value -> Ctx v -> Ctx (Maybe v)

eval :: Show v => Ctx v -> Exp v -> Value
eval ctx (Lam e) = Closure $ \a -> eval (Bind' a ctx) e
eval ctx (Var i) = lookupVar ctx i
  where
    lookupVar :: Ctx x -> x -> Value
    lookupVar EmptyCtx' v = case v of
    lookupVar (Bind' a _) Nothing = a
    lookupVar (Bind' _ as) (Just v) = lookupVar as v
eval ctx (App f x) =
  case (eval ctx f, eval ctx x) of
    (Closure vf, v) -> vf v
    _ -> error "Cannot call non-function"
eval ctx (Tuple a b) = Pair (eval ctx a) (eval ctx b)
eval _ Unit = UnitValue
eval _ (Const x) = Number x
eval _ (Type t) = TypeValue t
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
    go _ = error "Cannot add"
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

zeroTangent :: Type -> Value
zeroTangent TFloat = Number 0
zeroTangent (TTuple a b) = Pair (zeroTangent a) (zeroTangent b)
zeroTangent (TArr _ _) = error "No tangent for function"
zeroTangent TUnit = UnitValue

-- Treat Context as a heterogeneous list built up from tuples
-- TODO: Optimize convertVar with a proj primitive
convertVar :: Context v -> v -> Exp o
convertVar EmptyCtx v = case v of
convertVar (Bind _) Nothing = fstD
convertVar (Bind ctx) (Just v) = sequenceD sndD (convertVar ctx v)

-- (a -> a)
idD :: Exp a
idD = Tuple (Type TUnit) $ Lam (Tuple (Var Nothing) (Lam (Tuple Unit (Var Nothing))))

{-
   idD = \a -> (a, \db -> ((), db))
-}

-- b -> (a -> b)
constD :: Exp a -> Exp a
constD b = Tuple (Type TUnit) $ Lam body
  where
    {-
       constD b = \a -> (b, \db -> ((), zero a))
    -}
    pullback = Tuple Unit (Zero (Var (Just Nothing)))
    body = Tuple (shift b) (Lam pullback)

let' :: Exp a -> Exp (Maybe a) -> Exp a
let' x e = App (Lam e) x

shift :: Exp a -> Exp (Maybe a)
shift = fmap Just

fst' :: Exp a -> Exp a
fst' = App (Primitive Fst)

snd' :: Exp a -> Exp a
snd' = App (Primitive Snd)

add' :: Exp a -> Exp a
add' = App (Primitive Add)

mul' :: Exp a -> Exp a
mul' = App (Primitive Mul)

id' :: Exp a
id' = Lam (Var Nothing)

-- (a -> b) -> (b -> c) -> (a -> c)
sequenceD :: forall a. Exp a -> Exp a -> Exp a
sequenceD (Tuple (Type tx) f) (Tuple (Type ty) g) = Tuple (Type (TTuple tx ty)) $ Lam body
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
    a = Var Nothing
    b = fst' (Var Nothing)
    body =
      let' (App (shift f) a) $
        let' (App (shift $ shift g) b) (Tuple c (Lam pullback))
    c = fst' (Var Nothing)
    g' = snd' (Var (Just $ Just Nothing))
    f' = snd' (Var (Just $ Just $ Just $ Just Nothing))
    db = snd' (Var Nothing)
    x = fst' (Var Nothing)
    y = fst' (Var (Just Nothing))
    da = snd' (Var Nothing)
    pullback = let' (App g' (Var Nothing)) $ let' (App f' db) (Tuple (Tuple x y) da)
sequenceD _ _ = error "Cannot sequence"

-- (a -> b) -> (a -> c) -> (a -> (b,c))
fanOut :: Exp a -> Exp a -> Exp a
fanOut f g = sequenceD dupD (parallelD f g)

dupD :: Exp a
dupD = Tuple (Type TUnit) $ Lam (Tuple (Tuple a a) pullback)
  where
    {-
       dupD = \a -> ((a,a), \(da,db) -> ((), add (da,db)))
    -}
    a = Var Nothing
    p = Var Nothing
    pullback = Lam (Tuple Unit (add' p))

parallelD :: Exp a -> Exp a -> Exp a
parallelD (Tuple (Type tx) f) (Tuple (Type ty) g) = Tuple (Type (TTuple tx ty)) $ Lam body
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
    a = fst' (Var Nothing)
    c = snd' (Var Nothing)
    b = fst' (Var (Just Nothing))
    d = fst' (Var Nothing)
    body =
      let' (App (shift f) a) $
        let' (App (shift $ shift g) c) $
          Tuple (Tuple b d) (Lam pullback)
    f' = Var $ Just $ Just Nothing
    g' = Var $ Just $ Just Nothing
    db = fst' (Var Nothing)
    dd = snd' (Var (Just Nothing))
    x = fst' (Var (Just Nothing))
    da = snd' (Var (Just Nothing))
    y = fst' (Var Nothing)
    dc = snd' (Var Nothing)
    pullback =
      let' (App f' db) $
        let' (App g' dd) $
          Tuple (Tuple x y) (Tuple da dc)
parallelD _ _ = error "Cannot parallel"

-- (a -> b, a) -> b
applyD :: Exp a
applyD = Tuple (Type TUnit) $ Lam body
  where
    {-
       applyD = \(f,a) ->
        let (b,f') = f a
        in (b, \db -> ((), f' db))
    -}
    f = fst' (Var Nothing)
    a = snd' (Var Nothing)
    b = fst' (Var Nothing)
    body = let' (App f a) (Tuple b (Lam pullback))
    f' = snd' $ Var (Just Nothing)
    db = Var Nothing
    pullback = Tuple Unit (App f' db)

-- ((a,b) -> c) -> (a -> (b -> c))
curryD :: Exp a -> Exp a
curryD (Tuple (Type tx) f) = Tuple (Type tx) $ Lam body
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
    -}
    a = Var (Just Nothing)
    b = Var Nothing
    c = fst' (Var Nothing)
    f' = snd' (Var (Just Nothing))
    dc = Var Nothing
    x = fst' (Var Nothing)
    da = fst' $ snd' (Var Nothing)
    db = snd' $ snd' (Var Nothing)
    pullback = let' (App f' dc) (Tuple (Tuple x da) db)
    g = let' (App (shift $ shift f) (Tuple a b)) (Tuple c (Lam pullback))
    body = let' (Lam g) (Tuple (Var Nothing) id')
curryD _ = error "No curry"

fstD :: Exp a
fstD = Tuple (Type TUnit) $ Lam body
  where
    {-
       fstD = \(a,b) -> (a, \da -> ((), (da, zero b)))
    -}
    b = snd' (Var (Just Nothing))
    pullback = Tuple Unit (Tuple (Var Nothing) (Zero b))
    a = fst' (Var Nothing)
    body = Tuple a (Lam pullback)

sndD :: Exp a
sndD = Tuple (Type TUnit) $ Lam body
  where
    {-
       fstD = \(a,b) -> (b, \db -> ((), (zero a, db)))
    -}
    a = fst' (Var (Just Nothing))
    pullback = Tuple Unit (Tuple (Zero a) (Var Nothing))
    b = snd' (Var Nothing)
    body = Tuple b (Lam pullback)

addD :: Exp a
addD = Tuple (Type TUnit) $ Lam body
  where
    {-
       addD = \(a,b) -> (a + b, \dc -> ((), (dc, dc)))
    -}
    pullback = Tuple Unit (Tuple (Var Nothing) (Var Nothing))
    body = Tuple (add' (Var Nothing)) (Lam pullback)

mulD :: Exp a
mulD = Tuple (Type TUnit) $ Lam body
  where
    {-
       mulD = \(a,b) -> (a * b, \dc -> ((), (b * dc, a * dc)))
    -}
    dc = Var Nothing
    a = fst' (Var (Just Nothing))
    b = snd' (Var (Just Nothing))
    pullback = Tuple Unit (Tuple (mul' (Tuple b dc)) (mul' (Tuple a dc)))
    body = Tuple (mul' (Var Nothing)) (Lam pullback)
