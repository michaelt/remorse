{-# LANGUAGE ExistentialQuantification, GADTs, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}

module Remorse.Free where

import Remorse.FreeT (blank, maps, singleton, Queue)
import Data.TASequence (TAViewL(..), (><), tviewl)
import Control.Monad
import Control.Applicative
import Control.Arrow (Kleisli(..))
import Control.Monad.Trans 
import Control.Monad.Morph
import qualified Data.Foldable as F
import Data.Monoid
import Remorse.Of

data Free f a = forall x . 
    Free (Step f x)
          (Queue (Kleisli (Free f)) x a)

data Step f x = Stop x | Step (f (Free f x))


-- fold construct return = id
construct ::  f (Free f a)  -> Free f a
construct = \f -> Free (Step f) blank
{-# INLINE construct #-}

extend :: Queue (Kleisli (Free f)) x a
       -> Free f x 
       -> Free f a
extend t = \(Free h m) -> Free h (m >< t)
{-# INLINE extend #-}

kleisli :: (a -> Free f b) -> Queue (Kleisli (Free f)) a b
kleisli = singleton . Kleisli
{-# INLINE kleisli #-}

instance Functor (Free f) where
    {-# INLINE fmap #-}
    fmap f  = extend (kleisli (return . f))

instance Applicative (Free f) where
  pure x = Free (Stop x) blank
  (<*>) = ap

instance Monad (Free f) where
    return x = Free (Stop x) blank
    {-# INLINE return #-}
    Free s ks >> m = Free s (ks >< kleisli (\_ -> m))
    {-# INLINE (>>) #-}
    (Free s ks) >>= f = Free s (ks >< kleisli f)
    {-# INLINE (>>=) #-} 

instance MFunctor Free where
  hoist phi (Free step ks) = 
    Free (case step of Stop r  -> Stop r
                       Step ff -> Step (phi (liftM (hoist phi) ff))) 
         (mapKleislis (hoist phi) ks)

instance MMonad Free where
  embed phi (Free step ks) =
     do let ks' = maps (Kleisli . (embed phi .) . runKleisli) ks
        case step of 
          Stop x -> Free (Stop x) ks' 
          Step mx -> extend ks' (phi mx >>= embed phi) 

instance MonadTrans Free where
  lift ma = Free (Step (liftM return ma)) blank
  {-# INLINE lift #-}
  
instance (MonadIO m) => MonadIO (Free m) where
  liftIO  = construct . liftM return . liftIO 


expose :: (Functor f) => Free f r -> Step f r 
expose (Free step ks) = case step of
  Stop x -> case tviewl ks of 
    TAEmptyL         -> Stop x
    Kleisli f :< ks' -> expose (extend ks' (f x))
  Step f             -> Step (fmap (extend ks) f)
{-# INLINABLE expose #-}

uncons :: Functor f => Free f r -> Either r (f (Free f r))
uncons = freeMap Left Right

exposed :: (Functor f) => Free f r -> Free f (Either r (f (Free f r)))
exposed (Free step ks) = case step of
  Stop x -> case tviewl ks of 
    TAEmptyL         -> Free (Stop (Left x)) blank
    Kleisli f :< ks' -> exposed (extend ks' (f x))
  Step f             -> Free (Stop (Right (fmap (extend ks) f))) blank
{-# INLINABLE exposed #-}


fold :: (Functor f) 
     => (f x -> x)
     -> (a -> x)
     -> Free f a 
     -> x
fold construct done  = freeMap done (construct . (fmap (fold construct done)))


-- | Convert from a church-encoded version of Free
buildFree :: (Functor f) 
           => (forall x . (f x -> x) -> (r -> x) -> x)
           -> Free f r
buildFree phi = phi construct return

-- |  Convert to the default church encoding  
foldFree :: Functor f
         =>  Free f r 
         -> (forall x . (f x -> x) -> (r -> x) -> x)
foldFree free op out = fold op out free 
{-# INLINE foldFree #-}

-- rules :  foldFree (buildFree psi) = id

-- from extensible effects 
freeMap :: Functor f
             => (a -> t) -- ^ function to be applied if value is Pure
             -> (f (Free f a) -> t) -- ^ function to be applied on Impure value
             -> Free f a -- ^ Free value to be mapped over
             -> t -- ^ result
freeMap f g mx = case expose mx of
  Stop x -> f x
  Step u -> g u
{-# INLINE freeMap #-}

mapKleislis :: (forall x . Free f x -> Free g x)
            -> Queue (Kleisli (Free f)) a b 
            -> Queue (Kleisli (Free g)) a b
mapKleislis phi = maps (\(Kleisli f)  -> Kleisli (phi . f))
{-# INLINE mapKleislis #-}

transFree :: Functor f
           => (forall x . f x -> g x) 
           -> (forall a . Free f a -> Free g a)
transFree phi (Free step ks) = Free 
   (case step of Stop r  -> Stop r
                 Step ff -> Step (phi (fmap (transFree phi) ff)) ) 
   (mapKleislis (transFree phi) ks)                                                 
{-# INLINABLE transFree #-}


freeList :: [a] -> Free ((,) a) ()
freeList xs = buildFree (phi xs) where
  phi xs = \op out -> foldr (curry op) (out ()) xs

unFreeList :: Free ((,) a) r -> [a]
unFreeList = fold (uncurry (:)) (const [])