{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Implementation of `Eff` monad as described by "Freer Monads, More Extensible Effects" by Oleg
-- Kiselyov and Hiromi Ishii.
--
module Control.Monad.Eff
  ( Union (..)
  , decomp
  , Member
  , Arrs
  , Eff (..)
  , send
  , kApp
  , run
  , runM

    -- * Continuation queue
  , module Data.TAQueue
  ) where

import Data.TAQueue

----------------------------------------------------------------------------------------------------

-- | `r` is a type-level list of effect labels and `v` is type of return value. @Union r v@ is an
-- effectful value that returns `v`.
data Union (r :: [ * -> * ]) v where
  UNow  :: t v -> Union (t ': r) v
  UNext :: Union r v -> Union (any ': r) v

-- | From a union get a request labelled `t` or a smaller union without `t`.
decomp :: Union (t ': r) v -> Either (Union r v) (t v)
decomp (UNow  e) = Right e
decomp (UNext u) = Left u

----------------------------------------------------------------------------------------------------

data Nat = Z | S Nat

-- | Injecting/projecting at a specified position `n`.
class Member' (n :: Nat) (f :: * -> *) r where
  inj' :: f v -> Union r v
  prj' :: Union r v -> Maybe (f v)

instance (r ~ (t ': r')) => Member' 'Z t r where
  inj' = UNow
  prj' (UNow x) = Just x
  prj' _        = Nothing

instance Member' n t r' => Member' ('S n) t (t' ': r') where
  inj' v = UNext (inj' @n v)
  prj' UNow{}    = Nothing
  prj' (UNext u) = prj' @n u

----------------------------------------------------------------------------------------------------

class (Member' (FindElem t r) t r ) => Member t r where
  inj :: t v -> Union r v

instance (Member' (FindElem t r) t r ) => Member t r where
  inj = inj' @(FindElem t r)

----------------------------------------------------------------------------------------------------

type family FindElem (t :: * -> *) (r :: [ * -> * ]) :: Nat where
  FindElem t (t   ': r)  = 'Z
  FindElem t (any ': r)  = 'S (FindElem t r)

----------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------

-- | Composition of effectful functions. Final function maps `a` to `b` and also does effects
-- denoted by `r`.
type Arrs r a b = TAQueue (Eff r) a b

data Eff r a
  = Val a
      -- ^ A pure value.
  | forall x . Eff (Union r x) (Arrs r x a)
      -- ^ An effectful value and continuation.

instance Functor (Eff r) where
  fmap f (Val a)    = Val (f a)
  fmap f (Eff u as) = Eff u (snoc as (Val . f))

instance Applicative (Eff r) where
  pure = Val

  Val f   <*> Val a     = Val (f a)
  Val f   <*> Eff u  as = Eff u (snoc as (Val . f))
  Eff u k <*> Val a     = Eff u (snoc k (Val . ($ a)))
  Eff u k <*> Eff u' k' = Eff u (snoc k (\f -> Eff u' (snoc k' (\a -> Val (f a)))))

instance Monad (Eff r) where
  Val a    >>= f = f a
  Eff u as >>= f = Eff u (snoc as f)

-- | Apply value `a` to effectful continuation @Arrs r a b@.
kApp :: Arrs r a b -> a -> Eff r b
kApp k0 a =
    case viewl k0 of
      Singleton k -> k a
      Cons k t    -> app (k a) t
  where
    app :: Eff r x -> Arrs r x b -> Eff r b
    app (Val y)   k  = kApp k y
    app (Eff u k) k' = Eff u (append k k')

-- | Inject an effectful value into an `Eff`.
send :: Member t r => t v -> Eff r v
send t = Eff (inj t) (singleton Val)

-- | Run an `Eff`.
run :: Eff '[] a -> a
run (Val   x  ) = x
run (Eff u _) = case u of {}

-- | Run `Eff` in base monad `m`.
runM :: Monad m => Eff '[m] a -> m a
runM (Val a)     = return a
runM (Eff u k) =
  case decomp u of
    Right m  -> m >>= runM . kApp k
    Left  u' -> case u' of {}
