{-# LANGUAGE ExistentialQuantification, GADTs, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
module Remorse.FreeT where
  
import qualified Data.TASequence.FastCatQueue as T
import Data.TASequence (TAViewL(..), (><))
import Control.Monad
import Control.Applicative
import Control.Arrow (Kleisli(..))
import Control.Monad.Trans 
import Control.Monad.Morph

type Queue = T.FastTCQueue

uncons = T.tviewl
blank = T.tempty
maps = T.tmap
singleton :: T.TASequence s => c x y -> s c x y
singleton = T.tsingleton


data FreeT f m a = forall x . 
    FreeT (m (Step f m x))
          (Queue (Kleisli (FreeT f m)) x a)

data Step f m a = Stop a | Step (f (FreeT f m a))

construct :: Monad m 
       => f (FreeT f m a) 
       -> FreeT f m a
construct = \f -> FreeT (return (Step f)) blank
{-# INLINE construct #-}

wrap :: (Monad m, Functor f) 
     => m (FreeT f m a)
     -> FreeT f m a 
wrap = \mf -> FreeT (mf >>= next) blank
{-# INLINE wrap #-}

extend :: Queue (Kleisli (FreeT f m)) x a
       -> FreeT f m x 
       -> FreeT f m a
extend t = \(FreeT h m) -> FreeT h (m >< t)
{-# INLINE extend #-}

next :: (Functor f, Monad m) => FreeT f m r -> m (Step f m r)
next (FreeT mstep ks) = mstep >>= \case
  Stop x -> case uncons ks of 
    TAEmptyL            -> return (Stop x)
    Kleisli f :< ks' -> next (extend ks' (f x))
  Step f             -> return (Step (fmap (extend ks) f))
{-# INLINABLE next #-}

instance Monad m => Functor (FreeT f m) where
    {-# INLINE fmap #-}
    fmap f  = extend (singleton (Kleisli (return . f)))

instance Monad m => Applicative (FreeT f m) where
  pure x = FreeT (return (Stop x)) blank
  (<*>) = ap

instance Monad m => Monad (FreeT f m) where
    return x = FreeT (return (Stop x)) blank
    {-# INLINE return #-}
    FreeT m ks >> f = FreeT m (ks >< singleton (Kleisli (\_ -> f)))
    {-# INLINE (>>) #-}
    (FreeT m ks) >>= f = FreeT m (ks >< singleton (Kleisli f))
    {-# INLINE (>>=) #-} 


instance Functor f => MFunctor (FreeT f) where
  hoist = hoistFreeT

instance Functor f => MMonad (FreeT f) where
  embed phi = \(FreeT mstep ks) -> 
     do step <- phi mstep
        let ks' = maps (Kleisli . (embed phi .) . runKleisli) ks
        case step of 
          Stop x -> extend ks' (return x)
          Step fx -> extend ks' (construct (fmap (embed phi) fx))
          
instance Functor f => MonadTrans (FreeT f) where
  lift = \ma -> FreeT (ma >>= return . Stop) blank
  {-# INLINE lift #-}
  
instance (Functor f, MonadIO m) => MonadIO (FreeT f m) where
  liftIO  = wrap . liftM return . liftIO 

fold :: (Functor f, Monad m) 
     => (f x -> x)
     -> (m x -> x)
     -> (a -> x)
     -> FreeT f m a 
     -> x
fold construct wrap done free = foldFreeT free construct wrap done
{-# INLINABLE fold #-}

-- | Convert from a church-encoded version of FreeT

buildFreeT :: (Functor f, Monad m) 
           => (forall x . (f x -> x) -> (m x -> x) -> (r -> x) -> x)
           -> FreeT f m r
buildFreeT phi = phi construct wrap return

-- |  Convert to the default church encoding 

foldFreeT :: (Functor f, Monad m) 
           =>  FreeT f m r 
           -> (forall x . (f x -> x) -> (m x -> x) -> (r -> x) -> x)
foldFreeT free = \construct wrap done -> 
 let loop (FreeT mstep ks) = wrap $ do
      step <- mstep
      return $ case (step , uncons ks) of
       (Stop o, TAEmptyL)            -> done o
       (Stop o, Kleisli f :< ks') -> loop (extend ks' (f o))
       (Step ffo, TAEmptyL)          -> construct (fmap loop ffo)
       (Step ffo, _)              -> construct (fmap (loop . extend ks) ffo)
 in loop free




iterT ::  (Functor f, Monad m) 
      => (f (m a) -> m a) -> FreeT f m a -> m a
iterT phi = fold phi join return

iterTM :: (Functor f, Monad m, MonadTrans t, Monad (t m)) 
       =>  (f (t m a) -> t m a) -> FreeT f m a -> t m a
iterTM phi = fold phi (join . lift) (lift . return)

mapKleislis :: (forall x . FreeT f m x -> FreeT g  n x)
            -> Queue (Kleisli (FreeT f m)) a b 
            -> Queue (Kleisli (FreeT g n)) a b
mapKleislis phi = maps (\(Kleisli f)  -> Kleisli (phi . f))
{-# INLINE mapKleislis #-}

hoistFreeT :: (Monad m, Functor f) 
           => (forall x. m x -> n x) 
           -> FreeT f m a -> FreeT f n a
hoistFreeT phi (FreeT mstep ks) = FreeT 
  (phi $ do step <- mstep
            return $ case step of
              Stop r  -> Stop r
              Step ff -> Step (fmap (hoistFreeT phi) ff)  
  )
  (mapKleislis (hoistFreeT phi) ks)
{-# INLINABLE hoistFreeT #-}


transFreeT :: (Monad m, Functor f) 
           => (forall x . f x -> g x) 
           -> FreeT f m a -> FreeT g m a
transFreeT phi (FreeT mstep ks) = FreeT 
   (do step <- mstep 
       return $ case step of
          Stop r  -> Stop r
          Step ff -> Step (phi (fmap (transFreeT phi) ff))
   ) 
   (mapKleislis (transFreeT phi) ks)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   
{-# INLINABLE transFreeT #-}

enlist :: Monad m => [a] -> FreeT ((,) a) m ()
enlist [] = return ()
enlist (a:as) = construct (a,enlist as)

printer :: Show a => FreeT ((,) a) IO () -> IO ()
printer = fold (\(a,io) -> print a >> io) join return
-- cutoff ::
--   (Functor f, Monad m) =>
--   Integer -> FreeT f m a -> FreeT f m (Maybe a)