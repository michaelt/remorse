{-# LANGUAGE RankNTypes, ScopedTypeVariables, BangPatterns, DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Remorse.FreeT.Prelude 
  ( Of (..)
  , break 
  , break_ 
  , chunksOf 
  , concats 
  , drop 
  , dropWhile 
  , filter 
  , filterM 
  , for 
  , iterate 
  , iterateM 
  , map 
  , mapM 
  , prefor 
  , repeat 
  , repeatM 
  , replicate 
  , replicateM 
  , scanr 
  , span 
  , span_ 
  , splitAt 
  , sum 
  , sum_ 
  , take 
  , takeWhile 
  , unf 
  , yield
   ) where

import Remorse.FreeT
import Control.Monad hiding (mapM,replicateM,filterM)
import Control.Monad.Trans
import Prelude hiding (map, filter, drop, take, sum
                      , iterate, repeat, replicate, splitAt
                      , takeWhile, enumFrom, enumFromTo, span
                      , mapM, break, scanr, dropWhile)
import qualified Prelude as P
import Control.Arrow (Kleisli(..))
import Remorse.Of

yield :: Monad m => a -> FreeT (Of a) m ()
yield a = FreeT (return (Step (a :> return ()))) blank
{-# INLINE yield #-}

prefor :: (Monad m, Functor g, Functor f) 
       => (forall x . g x -> FreeT f m x) 
       -> FreeT g m r 
       -> FreeT f m r
prefor phi = concats . transFreeT phi


for free f = prefor (\(a :> x) -> f a >> return x) free

-- ---------------
-- sum 
-- ---------------
sum :: (Monad m) => FreeT (Of Int) m () -> m Int
sum = loop 0 where
  loop n free = do 
    step <- next free
    case step of 
      Stop _ -> return n
      Step (a :> rest) -> loop (n+a) rest
{-# INLINABLE sum #-}

--
sum_ :: (Monad m) => FreeT (Of Int) m () -> m Int
sum_ d = fold (\(a :> f) -> f >=> return . (+a) )
            (\mf n -> mf >>= \f -> f n)
            (\() m -> return m)
            d
            0
{-# INLINABLE sum_ #-}

-- ---------------
-- replicate 
-- ---------------

replicate :: (Monad m) => Int -> a -> FreeT (Of a) m ()
replicate n a  = loop n where -- take n . repeat -- loop n where
  loop 0 = return ()
  loop m = do yield a
              loop (m-1)
{-# INLINABLE replicate #-}


replicateM :: Monad m => Int -> m a -> FreeT (Of a) m ()
replicateM n ma = loop n where
  loop 0 = return ()
  loop m  = do a <- lift $ ma
               yield a
               loop (m-1)
{-# INLINABLE replicateM #-}



-- ---------------
-- iterate
-- ---------------

iterate :: Monad m => (a -> a) -> a -> FreeT (Of a) m r
iterate f = loop where
  loop a = do yield a
              loop (f a)
{-# INLINABLE iterate #-}


iterateM :: Monad m => (a -> m a) -> m a -> FreeT (Of a) m r
iterateM f ma = do a <- lift ma
                   loop a
  where
  loop a = do yield a
              a' <- lift (f a)
              loop a'  

{-# INLINABLE iterateM #-}



-- ---------------
-- repeat
-- ---------------

repeat :: Monad m => a -> FreeT (Of a) m r
repeat a = yield a >> repeat a
{-# INLINABLE repeat #-}

repeatM :: Monad m => m a -> FreeT (Of a) m r
repeatM ma = do a <- lift ma 
                yield a
                repeatM ma
{-# INLINABLE repeatM #-}

-- ---------------
-- filter 
-- ---------------

filter :: Monad m => (a -> Bool) -> FreeT (Of a) m r -> FreeT (Of a) m r
filter pred = loop where
  loop p = do n <- lift (next p)
              case n of Stop r -> return r
                        Step (a :> p') -> do when (pred a) (yield a )
                                             loop p'
{-# INLINABLE filter #-}


filterM :: Monad m => (a -> m Bool) -> FreeT (Of a) m r -> FreeT (Of a) m r
filterM pred = loop where
  loop p = do 
    n <- lift (next p)
    case n of 
      Stop r -> return r
      Step (a :> p') -> do 
        so <- lift (pred a)
        if so 
          then yield a >> loop p'
          else loop p'

-- ---------------
-- drop
-- ---------------

drop :: Monad m => Int -> FreeT (Of a) m r -> FreeT (Of a) m r
drop  = loop  where
  loop 0 p = p
  loop m p = do 
    step <- lift (next p)
    case step of 
      Stop r -> return r
      Step (a :> p') -> loop (m-1) p'
{-# INLINABLE drop #-}

dropWhile :: Monad m => (a -> Bool) -> FreeT (Of a) m r -> FreeT (Of a) m r
dropWhile pred = loop where
  loop p = do 
    step <- lift (next p)
    case step of 
      Stop r -> return r
      Step (a :> rest) -> 
        if pred a 
          then loop rest
          else yield a >> rest 
{-# INLINABLE dropWhile #-}


-- ---------------
-- take
-- ---------------


take :: (Monad m, Functor f) => Int -> FreeT f m r -> FreeT f m ()
take n = loop n where
  loop 0 p = return ()
  loop m p = do 
    step <- lift (next p)
    case step of 
      Stop r  -> return ()
      Step ff -> construct (fmap (loop (m-1)) ff)
{-# INLINABLE take #-}


takeWhile :: Monad m => (a -> Bool) -> FreeT (Of a) m r -> FreeT (Of a) m ()
takeWhile pred = loop where
  loop p = do 
    step <- lift (next p)
    case step of 
      Stop r -> return ()
      Step (a :> rest) -> if pred a 
                            then yield a >> loop rest
                            else return ()
{-# INLINABLE takeWhile #-}

-- -----
-- span break
-- -----


span_ :: (Monad m, Functor f) => (f (FreeT f m r) -> Bool) 
           -> FreeT f m r -> FreeT f m (FreeT f m r)
span_ pred = loop where
  loop p = do 
    step <- lift (next p)
    case step of 
      Stop r -> return (return r)
      Step frest -> 
        if pred frest 
          then construct (fmap loop frest) 
          else return (construct frest)
{-# INLINABLE span_ #-}
-- somehow 'pred' should be more interesting, e.g. (forall x . f x -> Maybe x)
break_
  :: (Functor f, Monad m) =>
     (f (FreeT f m r) -> Bool) -> FreeT f m r -> FreeT f m (FreeT f m r)
break_ pred = span_ (not . pred)

span :: Monad m 
       => (a -> Bool)
       -> FreeT (Of a) m r 
       -> FreeT (Of a) m (FreeT (Of a) m r)
span pred = span_ (\(a :> x) -> pred a)
break
  :: Monad m =>
     (a -> Bool)
     -> FreeT (Of a) m r -> FreeT (Of a) m (FreeT (Of a) m r)
break pred = span (not . pred)
-- ---------------
-- concats concat/join
-- ---------------

concats :: (Monad m, Functor f) => FreeT (FreeT f m) m r -> FreeT f m r
concats  = loop where
  loop p = do 
    step <- lift (next p)
    case step of 
      Stop r -> return r
      Step free -> do p' <- free
                      loop p'
{-# INLINABLE concats #-}

-- ---------------
-- map
-- ---------------

map :: Monad m => (a -> b) -> FreeT (Of a) m r -> FreeT (Of b) m r
map f = transFreeT (\(a :> rest) -> f a :> rest)
{-# INLINABLE map #-}

mapM :: Monad m => (a -> m b) -> FreeT (Of a) m r -> FreeT (Of b) m r
mapM f (FreeT mstep ks) =
     FreeT 
     (do step <- mstep 
         case step of
           Stop r  ->  return (Stop r)
           Step (a :> rest) -> do 
             b <- f a
             return (Step (b :> mapM f rest))
      )
     (mapKleislis (mapM f) ks)
{-# INLINABLE mapM #-}





scanr :: Monad m =>  (a -> b -> b) -> b 
      ->  FreeT (Of a) m r -> FreeT (Of b) m r
scanr op b = undefined


chunksOf :: Monad m 
         => Int 
         -> FreeT (Of a) m r 
         -> FreeT (FreeT (Of a) m) m r
chunksOf = undefined 
{-# INLINABLE chunksOf #-}


splitAt :: Monad m => Int -> FreeT (Of a) m r 
      -> FreeT (Of a) m (FreeT (Of a) m r)
splitAt n = loop n where
    loop 0 p = return p
    loop m p = do e <- lift (next p)
                  case e of 
                    Stop r -> return (return r)
                    Step (a:>p') -> loop (m-1) p
{-# INLINABLE splitAt #-}


unf :: (Functor f, Monad m)
       => (a -> m (Either r (f a))) -> a -> FreeT f m r
unf = undefined