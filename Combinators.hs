{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LiberalTypeSynonyms       #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE UndecidableSuperClasses   #-}

module Combinators where

import Prelude hiding (map)
import Data.Function
import Data.Either
import Control.Monad.Writer hiding (Any)
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Void
import Control.Monad
import Data.Char
import Data.List
import Data.Monoid hiding (Any)
import Text.Printf


import Categories
import CategoriesInstances
import Tambara


-- COMBINATORS

-- | Viewing is a profunctor that can be used to implement a 'view'
-- operation.  Viewing is a Tambara module for all the optics that
-- admit the 'view' operator.
newtype Viewing a b s t = Viewing { getView :: s -> a }
instance Profunctor Any (->) Any (->) (Viewing a b) where
  dimap l _ (Viewing f) = Viewing (f . l)

instance Tambara Any (->) Any (->) Any (->) (,) () (,) (,) (Viewing a b) where
  tambara (Viewing f) = Viewing (f . snd)

instance (Monad m) => Tambara Any (->) Any (->) (Algebra m) (->) (,) () (,) (,) (Viewing a b) where
  tambara = tambara @Any @(->) @Any @(->) @Any @(->) @(,) @()

-- | Previewing is a profunctor that can be used to implement a
-- 'preview' operation.  Previewing is a Tambara module for all the
-- optics that admit the 'preview' operator.
newtype Previewing a b s t = Previewing { getPreview :: s -> Maybe a }
instance Profunctor Any (->) Any (->) (Previewing a b) where
  dimap l _ (Previewing f) = Previewing (f . l)

instance Tambara Any (->) Any (->) Any (->) (,) () (,) (,) (Previewing a b) where
  tambara (Previewing f) = Previewing (f . snd)

instance Tambara Any (->) Any (->) Any (->) Either Void Either Either (Previewing a b) where
  tambara (Previewing f) = Previewing (either (\_ -> Nothing) f)

-- | Setting is a Tambara module for all the optics that admit the
-- 'set' operator.
newtype Setting a b s t = Setting { getSet :: (a -> b) -> (s -> t) }
instance Profunctor Any (->) Any (->) (Setting a b) where
  dimap l r (Setting f) = Setting (\u -> r . f u . l)

instance Tambara Any (->) Any (->) Any (->) (,) () (,) (,) (Setting a b) where
  tambara (Setting f) = Setting (\u (w,x) -> (w , f u x))

instance Tambara Any (->) Any (->) Any (->) Either Void Either Either (Setting a b) where
  tambara (Setting f) = Setting (\u -> either Left (Right . f u))

-- | Classifying is a Tambara module for all the optics that admit the
-- 'classify' operator.
newtype Classifying m a b s t = Classifying 
  { getClassify :: (Monad m) => m s -> b -> t }
instance (Monad m) => Profunctor Any (->) Any (->) (Classifying m a b) where
  dimap l r (Classifying f) = Classifying (\u -> r . f (fmap l u))

instance (Monad m) => Tambara Any (->) Any (->) (Algebra m) (->) (,) () (,) (,) (Classifying m a b) where 
  tambara (Classifying f) = Classifying (\w b -> (algebra (fmap fst w) , f (fmap snd w) b))

-- The class of profunctors that admit the 'aggregate' operator.
newtype Aggregating a b s t = Aggregate
  { getAggregate :: [s] -> ([a] -> b) -> t }
instance Profunctor Any (->) Any (->) (Aggregating a b) where
  dimap l r (Aggregate f) = Aggregate (\v u -> r $ f (fmap l v) u)

instance Tambara Any (->) Any (->) (Algebra []) (->) (,) () (,) (,) (Aggregating a b) where
  tambara (Aggregate u) = Aggregate (\l f -> (algebra (fmap fst l) , u (fmap snd l) f))

instance Tambara Any (->) Any (->) Applicative Nat Compose Identity App App (Aggregating a b) where
  tambara (Aggregate h) = Aggregate (\u f -> App $ pure (flip h f) <*> sequenceA (fmap getApp u))

-- The class of profunctors that admit the 'update' operator.
newtype Updating m a b s t = Update
  { getUpdate :: (Monad m) => b -> s -> m t }
instance (Monad m) => Profunctor Any (->) Any (->) (Updating m a b) where
  dimap l r (Update u) = Update (\b x -> fmap r (u b (l x)))
instance (Monad m) => Profunctor Any (->) Any (Kleisli m) (Updating m a b) where
  dimap l (Kleisli r) (Update u) = Update (\b x -> u b (l x) >>= r)

instance (Monad m) => Tambara Any (->) Any (Kleisli m) (Any) (->) (,) () (,) (,) (Updating m a b) where
  tambara (Update u) = Update (\b (w , x) -> fmap ((,) w) $ u b x)

-- The class of profunctors that admit the 'over' operator.
newtype Replacing a b s t = Replace
  { getReplace :: (a -> b) -> (s -> t) }
instance Profunctor Any (->) Any (->) (Replacing a b) where
  dimap l r (Replace u) = Replace (\f -> r . u f . l)

instance Tambara Any (->) Any (->) Any (->) (,) () (,) (,) (Replacing a b) where
  tambara (Replace u) = Replace (fmap . u)
instance Tambara Any (->) Any (->) Any (->) Either Void Either Either (Replacing a b) where
  tambara (Replace u) = Replace (fmap . u)
instance Tambara Any (->) Any (->) Functor Nat Compose Identity App App (Replacing a b) where
  tambara (Replace u) = Replace ((\f -> App . fmap f . getApp) . u)
instance Tambara Any (->) Any (->) Applicative Nat Compose Identity App App (Replacing a b) where
  tambara = tambara @Any @(->) @Any @(->) @Functor @Nat @Compose @Identity @App @App @(Replacing a b)
instance Tambara Any (->) Any (->) Traversable Nat Compose Identity App App (Replacing a b) where
  tambara = tambara @Any @(->) @Any @(->) @Functor @Nat @Compose @Identity @App @App @(Replacing a b)


-- | Inspired by the "view" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 ^.
(^.) :: s -> (Viewing a b a b -> Viewing a b s t) -> a
(^.) s l = getView (l $ Viewing id) s

-- | Inspired by the "preview" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 ?.
(?.) :: s -> (Previewing a b a b -> Previewing a b s t) -> Maybe a
(?.) s l = getPreview (l $ Previewing return) s

-- | Inspired by the "set" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 .~
(.~) :: (Setting a b a b -> Setting a b s t) -> b -> s -> t
(.~) l b = getSet (l $ Setting id) (\_ -> b)

-- | Inspired by the "over" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 %~
(%~) :: (Replacing a b a b -> Replacing a b s t) -> (a -> b) -> (s -> t)
(%~) l f = getReplace (l $ Replace id) $ f

-- | A "classify" operator. The fixity and semantics are such that
-- subsequent field accesses can be performed with 'Prelude..'.
infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = getClassify (l $ Classifying (\a b -> b)) ms b

-- | An "aggregate" operator. The fixity and semantics are such that
-- subsequent field accesses can be performed with 'Prelude..'.
infixl 8 >-
(>-) :: (Aggregating a b a b -> Aggregating a b s t) -> ([a] -> b) -> [s] -> t
(>-) l = flip $ getAggregate (l $ Aggregate $ flip ($))

-- | An "mupdate" operator. It is prepared to be used with do notation.
mupdate :: (Monad m) => (Updating m a b a b -> Updating m a b s t) -> b -> s -> m t
mupdate f = getUpdate $ f (Update (\b a -> return b))
