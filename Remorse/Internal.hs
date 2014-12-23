{-# LANGUAGE GADTs, LambdaCase, BangPatterns#-}
-- Author : Atze van der Ploeg 
-- A purely functional catenable queue representation with
-- that turns takes a purely functional queue and turns in it into
-- a catenable queue, i.e. with the same complexity for (><) as for (|>)
-- Based on Purely functional data structures by Chris Okasaki 
-- section 7.2: Catenable lists

module Remorse.Internal where
import Remorse.Sequence
import Control.Arrow (Kleisli (..))

data RTQueue tc a b where
  RQ :: !(Cons tc a b) -> !(Snoc tc b c) -> !(Cons tc x b) -> RTQueue tc a c

queue :: Cons tc a b -> Snoc tc b c -> Cons tc x b -> RTQueue tc a c
queue f r = \case Nil      -> let f' = rotate f r Nil 
                              in RQ f' Begin f'
                  Cons h t -> RQ f r t
{-# INLINE queue #-}

revAppend :: Cons tc a b  -> Snoc tc b d -> Cons tc a d
revAppend l r = rotate l r Nil
-- precondtion : |a| = |f| - (|r| - 1)
-- postcondition: |a| = |f| - |r=of90

rotate :: Cons tc a b -> Snoc tc b c -> Cons tc c d -> Cons tc a d
rotate Nil  (Begin `Snoc` y) r = y `Cons` r
rotate (x `Cons` f) (r `Snoc` y) a = x `Cons` rotate f r (y `Cons` a)
rotate f        a     r  = error "Invariant |a| = |f| - (|r| - 1) broken"
{-# INLINABLE rotate #-}

instance Sequence RTQueue where
  blank = RQ Nil Begin Nil
  {-# INLINE blank #-}
  singleton x = RQ (Cons x Nil) Begin Nil
  {-# INLINE singleton #-}
  (RQ f r a) |> x = queue f (r `Snoc` x) a
  {-# INLINE (|>) #-}
  
  uncons (RQ Nil Begin Nil) = Empty
  uncons (RQ (h `Cons` t) f a) = h :| queue t f a
  {-# INLINE uncons #-}

instance Maps RTQueue where
  maps phi (RQ a b c) = RQ (maps phi a) (maps phi b) (maps phi c)

data Queue c x y where
   Q0 :: Queue c x x
   QN :: c x e -> !(RTQueue (Queue c) e y) -> Queue c x y

instance Sequence Queue where
  blank       = Q0
  {-# INLINE blank #-}
  singleton a = QN a blank
  {-# INLINE singleton #-}
  Q0        >< ys   = ys
  xs        >< Q0   = xs
  (QN x q)  >< ys   = QN x (q |> ys)
  {-# INLINE (><) #-}
  Q0  |> a          = QN a blank
  QN x q  |> a      = QN x (q |> singleton a)
  {-# INLINE (|>) #-}
  uncons Q0         = Empty
  uncons (QN h rt)  = h :| loop rt where
    loop :: RTQueue (Queue c) a b -> Queue c a b
    loop !v = case uncons v of
      Empty      -> Q0
      QN x q :| u  -> QN x $ case loop u of Q0 -> q
                                            r  -> q |> r
  {-# INLINABLE uncons #-}
instance Maps Queue where 
  maps phi Q0 = Q0
  maps phi (QN a r) = QN (phi a) (maps (maps phi) r)
  {-# INLINABLE maps #-}





-- data CTQueue q c x y where
--    C0 :: CTQueue q c x x
--    CN :: c x e -> !(q (CTQueue q c) e y) -> CTQueue q c x y
-- 
-- 
-- instance Sequence q => Sequence (CTQueue q) where
--     blank       = C0
--     singleton a = CN a blank
--     C0        >< ys   = ys
--     xs        >< C0   = xs
--     (CN x q)  >< ys   = CN x (q |> ys)
-- 
--     uncons C0             = Empty
--     uncons (CN h t)  = h :| linkAll t
-- 
-- linkAll :: Sequence q =>  q (CTQueue q c) a b -> CTQueue q c a b
-- linkAll v = case uncons v of
--     Empty      -> C0
--     CN x q :| t  -> CN x (q `snoc` linkAll t)
--   where
--     snoc q C0  = q
--     snoc q r   = q |> r
-- 
