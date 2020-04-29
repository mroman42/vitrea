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

{-|
Module      : Optics
Description : Describing optics in terms of monoidal actions.
Copyright   : (c) Mario Román, 2020
License     : GPL-3
Maintainer  : mromang08@gmail.com
Stability   : experimental
Portability : POSIX

Obtains the common optics and some new ones as particular cases of the unified
definition of optic. This definition has been studied by Milewski ("Profunctor
optics, the categorical view", 2016), then by Boisseau and Gibbons ("What you
needa know about Yoneda", 2017), then by Riley ("Categories of optics", 2018),
and in the mixed enriched case we implement by Clarke, Elkins, Gibbons,
Loregian, Milewski, Pillmore and Román ("Profunctor optics, a categorical
update", 2019).
-}


module Optics where

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

-- | Lenses are optics for the action of the category on itself via the
-- cartesian product.
type Lens a s = ProfOptic Any (->) Any (->) Any (->) (,) () (,) (,) a a s s
mkLens :: (s -> a) -> (s -> a -> s) -> Lens a s
mkLens v u =
  ex2prof @Any @(->) @Any @(->) @Any @(->) @(,) @()
  $ Optic (\a -> (a , v a)) (\(s,b) -> u s b)

-- | Type-variant version.
type Lens' a b s t = ProfOptic Any (->) Any (->) Any (->) (,) () (,) (,) a b s t
mkLens' :: (s -> a) -> (s -> b -> t) -> Lens' a b s t
mkLens' v u =
  ex2prof @Any @(->) @Any @(->) @Any @(->) @(,) @()
  $ Optic (\a -> (a , v a)) (\(s,b) -> u s b)


-- | Prisms are optics for the action of the category on itself via the
-- coproduct.
type Prism a s = ProfOptic Any (->) Any (->) Any (->) Either Void Either Either a a s s
mkPrism :: (s -> Either s a) -> (a -> s) -> Prism a s
mkPrism m b = 
  ex2prof @Any @(->) @Any @(->) @Any @(->) @Either @Void
  $ Optic m (either id b)

-- | Algebraic lenses are optics for the action of the category of algebras of a
-- monad.
type AlgebraicLens m a s = (Monad m) => ProfOptic Any (->) Any (->) (Algebra m) (->) (,) () (,) (,) a a s s
mkAlgebraicLens :: forall m a s . (Monad m) => (s -> a) -> (m s -> a -> s) -> AlgebraicLens m a s
mkAlgebraicLens v u =
  ex2prof @Any @(->) @Any @(->) @(Algebra m) @(->) @(,) @()
  $ Optic (\a -> (return a , v a)) (\(ms,b) -> u ms b)

-- | Kaleidoscopes are optics for the action by evaluation of applicative
-- functors.
type Kaleidoscope a s = ProfOptic Any (->) Any (->) Applicative Nat Compose Identity App App a a s s
mkKaleidoscope :: (([a] -> a) -> ([s] -> s)) -> Kaleidoscope a s
mkKaleidoscope f =
  ex2prof @Any @(->) @Any @(->) @Applicative @Nat @Compose @Identity @App @App
  $ Optic (App . flip More (Done id)) (uncurry (flip f) . noFun . getApp)
    where
      noFun :: FunList s a b -> ([s] , ([a] -> b))
      noFun (Done b) = ([] , const b)
      noFun (More s l) = (\(u , f) -> (s:u , \(h:t) -> f t h)) $ noFun l

-- | Monadic lenses are mixed optics for the cartesian product in the base
-- category and in the Kleisli category.
type MonadicLens m a b s t = (Monad m) => ProfOptic Any (->) Any (Kleisli m) Any (->) (,) () (,) (,) a b s t
mkMonadicLens :: forall m a b s t . (Monad m) => (s -> a) -> (s -> b -> m t) -> MonadicLens m a b s t
mkMonadicLens v u =
  ex2prof @Any @(->) @Any @(Kleisli m) @Any @(->) @(,) @() @(,) @(,)
  $ Optic (\a -> (a , v a)) (Kleisli (uncurry u))

-- | Traversals as optics for the action of traversable functors.
type Traversal a s = ProfOptic Any (->) Any (->) Traversable Nat Compose Identity App App a a s s
mkTraversal :: forall a b s t . (s -> ([a], [a] -> s)) -> Traversal a s
mkTraversal ext = mkTraversal2 (\s -> Split (fst (ext s)) s) (\(Split la s) -> snd (ext s) la)

data Split s a = Split [a] s
instance Functor (Split s) where
  fmap f (Split l s) = Split (fmap f l) s
instance Foldable (Split s) where
  foldr f z (Split l s) = foldr f z l
instance Traversable (Split s) where
  traverse f (Split l s) = fmap (flip Split s) (traverse f l)


mkTraversal2 :: forall a s f . Traversable f => (s -> f a) -> (f a -> s) -> Traversal a s
mkTraversal2 l r =
  ex2prof @Any @(->) @Any @(->) @Traversable @Nat @Compose @Identity @App @App
  $ Optic (App . l) (r . getApp)
