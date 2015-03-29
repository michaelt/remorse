module Remorse.Of where

data Of a x = !a :> x deriving (Show, Read, Eq, Ord)

instance Functor (Of a) where
  fmap f  = \(a :> b) -> (a :> f b)
  {-# INLINE fmap #-}

strictPair (a,b) = a :> b
{-# INLINE strictPair #-}

lazyPair (a :> b) = (a,b)
{-# INLINE lazyPair #-}

kurry f a b = f (a :> b)
{-# INLINE kurry #-}

unkurry f (a:> b) = f a b
{-# INLINE unkurry #-}
