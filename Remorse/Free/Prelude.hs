{-# LANGUAGE GADTs, BangPatterns, RankNTypes, LambdaCase #-}
module Remorse.Free.Prelude where

import Remorse.Free
import Remorse.Of
import qualified Remorse.FreeT.Prelude as R
import Data.TASequence (TAViewL(..), (><), tviewl)
import Remorse.FreeT.Prelude (Of (..))
import Remorse.FreeT (blank, maps, singleton, Queue)
import Control.Monad hiding (mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Prelude hiding (map, filter, drop, take, sum
                      , iterate, repeat, replicate, splitAt
                      , takeWhile, enumFrom, enumFromTo, span, mapM, break)
import qualified Prelude as P
import Control.Arrow (Kleisli(..), (>>>))
import Control.Monad.Morph
import Data.Monoid


yield :: Functor f  => f x -> Free f x
yield fa = Free (Step (fmap return fa)) blank
{-# INLINE yield #-}

-- ---------------
-- sum 
-- ---------------
sum :: Free (Of Int) () -> Int
sum = fold (unkurry (+)) (const 0)

-- ---------------
-- replicate 
-- ---------------

replicate :: (Functor f, Monoid o) => Int -> f o -> Free f o
replicate n act = loop n mempty where
  loop 0 !o = return o
  loop n o  = Free (Step (fmap (return . (o <>)) act))
                   (kleisli (loop (n-1)))
{-# INLINABLE replicate #-}

replicateOf :: Int -> a -> Free (Of a) ()
replicateOf n = replicate n . (:> ())

-- ---------------
-- iterate
-- ---------------

iterate :: Functor f => (a -> f a) -> a -> Free f r
iterate f = loop where
  loop a = extend (kleisli loop) (yield (f a))
{-# INLINABLE iterate #-}

-- unfoldr uncons = id
unfoldr :: Functor f => (a -> Either r (f a)) -> a -> Free f r
unfoldr next = loop where
  loop = either return  (extend (kleisli loop) . yield)  . next 
{-# INLINABLE  unfoldr #-}


-- ---------------
-- repeat
-- ---------------

repeat :: Functor f => f x -> Free f r
repeat a = loop () where
  loop () = Free (Step (fmap (const (return ())) a)) 
                 (kleisli loop)
{-# INLINABLE repeat #-}

-- ---------------
-- filter 
-- ---------------



-- ---------------
-- drop
-- ---------------

-- drop :: Monad m => Int -> Producer a m r -> Producer a m r
-- drop  = loop  where
--   loop 0 p = p
--   loop m p = do 
--     step <- lift_ (next p)
--     case step of 
--       Left r -> return r
--       Right (a :> p') -> loop (m-(1::Int)) p'
-- {-# INLINABLE drop #-}

-- dropWhile :: Monad m => (a -> Bool) -> FreeT (Of a) m r -> FreeT (Of a) m r
-- dropWhile pred = loop where
--   loop p = do 
--     step <- lift (next p)
--     case step of 
--       Stop r -> return r
--       Step (a :> rest) -> 
--         if pred a 
--           then loop rest
--           else yield a >> rest 
-- {-# INLINABLE dropWhile #-}


-- ---------------
-- take
-- ---------------
 
take :: Functor f => Int -> Free f r -> Free f ()
take = loop where
  loop 0 p = return ()
  loop m p = case expose p of
      Stop r  -> return ()
      Step ff -> construct (fmap (loop (m-1)) ff)
{-# INLINABLE take #-}


-- takeWhile :: Monad m => (a -> Bool) -> FreeT (Of a) m r -> FreeT (Of a) m ()
-- takeWhile pred = loop where
--   loop p = do 
--     step <- lift (next p)
--     case step of 
--       Stop r -> return ()
--       Step (a :> rest) -> if pred a 
--                             then yield a >> loop rest
--                             else return ()
-- {-# INLINABLE takeWhile #-}

-- -- -----
-- -- span break
-- -- -----

-- span_ :: (Monad m, Functor f) => (f (FreeT f m r) -> Bool) 
--            -> FreeT f m r -> FreeT f m (FreeT f m r)
-- span_ pred = loop where
--   loop p = do 
--     step <- lift (next p)
--     case step of 
--       Stop r -> return (return r)
--       Step frest -> 
--         if pred frest 
--           then construct (fmap loop frest) 
--           else return (construct frest)
-- {-# INLINABLE span_ #-}

-- -- somehow 'pred' should be more interesting, e.g. (forall x . f x -> Maybe x)
-- break_
--   :: (Functor f, Monad m) =>
--      (f (FreeT f m r) -> Bool) -> FreeT f m r -> FreeT f m (FreeT f m r)
-- break_ pred = span_ (not . pred)
-- 
-- span :: Monad m 
--        => (a -> Bool)
--        -> FreeT (Of a) m r 
--        -> FreeT (Of a) m (FreeT (Of a) m r)
-- span pred = span_ (\(a :> x) -> pred a)
-- break
--   :: Monad m =>
--      (a -> Bool)
--      -> FreeT (Of a) m r -> FreeT (Of a) m (FreeT (Of a) m r)
-- break pred = span (not . pred)

-- ---------------
-- concats concat/join
-- ---------------

concats :: Functor f => Free (Free f) r -> Free f r
concats f0 = case expose f0 of 
  Stop r -> return r
  Step ff -> do f1 <- ff 
                concats f1

-- mapM :: Monad m => (a -> m b) -> FreeT (Of a) m r -> FreeT (Of b) m r
-- mapM f (FreeT mstep ks) =
--      FreeT 
--      (do step <- mstep 
--          case step of
--            Stop r  ->  return (Stop r)
--            Step (a :> rest) -> do 
--              b <- f a
--              return (Step (b :> mapM f rest))
--       )
--      (mapKleislis (mapM f) ks)
-- {-# INLINABLE mapM #-}
-- 
-- 
-- 
-- 
-- 
-- scanr :: Monad m =>  (a -> b -> b) -> b 
--       ->  FreeT (Of a) m r -> FreeT (Of b) m r
-- scanr op b = undefined
-- 
-- 
-- chunksOf :: Monad m 
--          => Int 
--          -> FreeT (Of a) m r 
--          -> FreeT (FreeT (Of a) m) m r
-- chunksOf = undefined 
-- {-# INLINABLE chunksOf #-}
-- chunksOf n = loop where
--   loop p = construct (fmap handle (expose (splitAtF n p)))
--   handle :: Int
--   handle = undefined

-- --------
-- splitAt
-- --------

splitAt :: Functor f => Int -> Free f r -> Free f (Free f r)
splitAt n = loop n where
  loop 0 p = return p
  loop m p = case expose p of
      Stop r  -> return (return r)
      Step ff -> construct (fmap (loop (m-1)) ff)
{-# INLINABLE splitAt #-}



