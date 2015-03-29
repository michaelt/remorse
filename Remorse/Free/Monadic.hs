{-# LANGUAGE GADTs, BangPatterns, RankNTypes, LambdaCase #-}
module Remorse.Free.Monadic where

import Remorse.Free
import qualified Remorse.FreeT.Prelude as R
import Data.TASequence (TAViewL(..), (><), tviewl)
import Remorse.Of
import Remorse.FreeT (blank, maps, singleton, Queue)
import Control.Monad hiding (mapM)
import Control.Monad.Trans
import Prelude hiding (map, filter, drop, take, sum
                      , iterate, repeat, replicate, splitAt
                      , takeWhile, enumFrom, enumFromTo, span, mapM, break)
import qualified Prelude as P
import Control.Arrow (Kleisli(..), (>>>))
import Control.Monad.Morph
import Data.Monoid

data With f m r = None (m r) | With (f r)

instance (Functor f, Monad m) => Functor (With f m) where 
  fmap f = \case None ma -> None (liftM f ma)
                 With fa -> With (fmap f fa)
  {-# INLINE fmap #-}

instance (Functor f) => MFunctor (With f) where
  hoist phi =  \case None ma -> None (phi ma)
                     With fa -> With fa

type FreeT f m = Free (With f m)
type Producer a m  = FreeT (Of a) m

none :: m (FreeT f m x) -> Step (With f m) x
none = Step . None 
{-# INLINE none #-}

with :: f (FreeT f m x) -> Step (With f m) x
with = Step . With
{-# INLINE with #-}


next :: (Functor f, Monad m) 
     => FreeT f m r -> m (Either r (f (FreeT f m r)))
next (Free step ks) = case step of
         Stop x -> case tviewl ks of 
           TAEmptyL         -> return (Left x)
           Kleisli f :< ks' -> next  (extend ks' (f x))
         Step (None m)      -> m >>= next  . extend ks
         Step (With f)     -> return (Right (fmap (extend ks) f))

advance :: (Functor f, Monad m) 
        => FreeT f m r  -> FreeT f m (Either r (f (FreeT f m r)))
advance (Free step ks) = case step of 
  Stop x -> case tviewl ks of 
    TAEmptyL         -> return (Left x)
    Kleisli f :< ks' -> case f x of Free a b -> advance (Free a (b >< ks'))
  Step (None m)      -> let more = \(Free a b) -> advance (Free a (b >< ks))
                        in Free (none (liftM more m)) blank
  Step (With f)      -> return (Right (fmap (extend ks) f))

yield :: Monad m => a -> Producer a m ()
yield a = Free (Step (With (a :> return ()))) blank
{-# INLINE yield #-}

lift_ :: Monad m => m a -> FreeT f m a
lift_ ma = Free (Step (None (liftM return ma))) blank
{-# INLINE lift_ #-}

freeTMap :: (Functor f, Monad m)
             => (a -> t) -- ^ function to be applied if value is Pure
             -> (f (FreeT f m a) -> t) -- ^ function to be applied on Impure value
             -> (m (FreeT f m a) -> t)
             -> FreeT f m a -- ^ Free value to be mapped over
             -> t -- ^ result
freeTMap f g h mx = case expose mx of
    Stop a        -> f a
    Step (None m) -> h m
    Step (With s) -> g s
{-# INLINE freeTMap #-}


foldFreeT :: (Functor f, Monad m)
           => (a -> x) -> (f x -> x) -> (m x -> x)  
           -> FreeT f m a -> x
foldFreeT f g h = loop where
   loop =  freeTMap f (\ffree -> g (fmap loop ffree )) 
                      (\mfree -> h (liftM loop mfree))

foldT :: (Functor f, Monad m)
      => FreeT f m a 
      -> (forall x . (a -> x) -> (f x -> x)  -> (m x -> x) -> x )
foldT free f g h  = loop free where
  loop = (\case Stop a        -> f a
                Step (None m) -> h (liftM loop m)
                Step (With s) -> g (fmap loop s) ) 
         . expose

-- ---------------
-- sum 
-- ---------------

summ :: (Monad m) => Producer Int m () -> m Int
summ = loop 0 where
  loop !n !free = do 
    step <- next free
    case step of 
      Left _ -> return n
      Right (a :> rest) -> loop (n+a) rest
{-# INLINABLE summ #-}

sum :: (Monad m) => Producer Int m () -> m Int
sum p = foldT p 
         (\_ n -> return n)
         (\(a :> f) n -> f $! (n+a))
         (\mf n -> mf >>= \f -> f n)
        0
{-# INLINE sum #-}

-- ---------------
-- replicate 
-- ---------------

replicateF :: (Functor f, Monoid o) => Int -> f o -> Free f o
replicateF n act = loop n mempty where
  loop 0 !o = return o
  loop n o  = Free (Step (fmap (return . (o <>)) act))
                   (kleisli (loop (n-1)))
{-# INLINABLE replicateF #-}

replicate :: Monad m => Int -> a -> Producer a m ()
replicate n a = loop n where 
  loop 0 = return ()
  loop m = Free (Step (With (a :> return m))) 
                (kleisli (\n -> loop (n - (1::Int))))
{-# INLINABLE replicate #-}

replicate_ :: Monad m => Int -> a -> Producer a m ()
replicate_ n a = extend (kleisli (\_ -> return ())) (loop n) where 
  loop 0 = return ()
  loop m = yield a >> loop (m - (1::Int))
{-# INLINABLE replicate_ #-}
-- loop a () = extend (kleisli (loop (f a))) (yield a)

replicateM :: Monad m => Int -> m a -> Producer a m ()
replicateM n ma = loop n where
  loop 0 = return ()
  loop m  = do a <- lift_ ma
               yield a
               loop (m-1)
{-# INLINABLE replicateM #-}

-- ---------------
-- iterate
-- ---------------

iterate :: Monad m => (a -> a) -> a -> Producer a m r
iterate f a = loop a () where
  loop a () = extend (kleisli (loop (f a))) (yield a)
{-# INLINABLE iterate #-}


iterateM :: Monad m => (a -> m a) -> m a -> Producer a m r
iterateM f ma = do a <- lift_ ma
                   loop a
  where
  loop a = do yield a
              a' <- lift_ (f a)
              loop a'  
{-# INLINABLE iterateM #-}

-- ---------------
-- repeat
-- ---------------

repeat :: Monad m => a -> Producer a m r
repeat a = loop () where
  loop () = Free (with (a :> return ())) 
                 (kleisli loop)
{-# INLINABLE repeat #-}

repeatF :: Functor f => f () -> Free f r
repeatF a = loop () where
  loop () = Free (Step (fmap return a)) 
                 (kleisli loop)
{-# INLINABLE repeatF #-}

repeatM :: Monad m => m a -> Producer a m r
repeatM ma = loop () where 
  loop () = Free (none (liftM yield ma))
                 (kleisli loop)
{-# INLINABLE repeatM #-}

-- -- ---------------
-- -- filter 
-- -- ---------------

filter_ :: Monad m => (a -> Bool) -> Producer a m r -> Producer a m r
filter_ pred = loop where
  loop p = do n <- lift_ (next p)
              case n of 
                Left r -> return r
                Right (a :> p') -> do when (pred a) (yield a )
                                      loop p'
{-# INLINABLE filter_ #-}

filter :: Monad m => (a -> Bool) -> Producer a m r -> Producer a m r
filter pred p = foldT p
  (\r p -> return r)
  (\(a :> f) p -> if p a then yield a >> f p else f p)
  (\mf p -> construct $ None (mf >>= \f -> return (f p)))
  pred
{-# INLINE filter #-}
--
-- foldT free f g h  = loop free where
--   loop = (\case
--       Stop a        -> f a
--       Step (None m) -> h (liftM loop m)
--       Step (With s) -> g (fmap loop s) ) . expose

filterM :: Monad m => (a -> m Bool) -> Producer a m r -> Producer a m r
filterM pred = loop where
  loop p = do 
    n <- lift_ (next p)
    case n of 
      Left r -> return r
      Right (a :> p') -> do 
        so <- lift_ (pred a)
        if so 
          then yield a >> loop p'
          else loop p'

-- ---------------
-- drop
-- ---------------

drop :: Monad m => Int -> Producer a m r -> Producer a m r
drop  = loop  where
  loop 0 p = p
  loop m p = do 
    step <- lift_ (next p)
    case step of 
      Left r -> return r
      Right (a :> p') -> loop (m-(1::Int)) p'
{-# INLINABLE drop #-}

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
-- 
-- 
-- ---------------
-- take
-- ---------------
 
take :: Functor f => Int -> Free f r -> Free f ()
take n = loop n where
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
-- 
-- -- -----
-- -- span break
-- -- -----
-- 
-- 
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

-- ---------------
-- map
-- ---------------

map :: Monad m => (a -> b) -> Producer a m r -> Producer b m r
map f = transFree (\case With (a :> rest) -> With (f a :> rest)
                         None m           -> None m) 
{-# INLINABLE map #-}

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

splitAtF :: Functor f => Int -> Free f r -> Free f (Free f r)
splitAtF n = loop n where
  loop 0 p = return p
  loop m p = case expose p of
      Stop r  -> return (return r)
      Step ff -> construct (fmap (loop (m-1)) ff)
{-# INLINABLE splitAtF #-}

splitAt :: Monad m => Int -> Producer a m r -> Producer a m (Producer a m r)
splitAt n = loop n where
  loop 0 p = return p
  loop m p = do e <- lift_ (next p)
                case e of 
                  Left r -> return (return r)
                  Right (a:>p') -> do yield a
                                      loop (m-1) p'
{-# INLINABLE splitAt #-}



