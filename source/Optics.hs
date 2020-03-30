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

-- Lenses are optics for the action of the category on itself via the
-- cartesian product.
type Lens a s = ProfOptic Any (->) Any (->) Any (->) (,) () (,) (,) a a s s
mkLens :: (s -> a) -> (s -> a -> s) -> Lens a s
mkLens v u =
  ex2prof @Any @(->) @Any @(->) @Any @(->) @(,) @()
  $ Optic (\a -> (a , v a)) (\(s,b) -> u s b)

-- Prisms are optics for the action of the category on itself via the
-- coproduct.
type Prism a s = ProfOptic Any (->) Any (->) Any (->) Either Void Either Either a a s s
mkPrism :: (s -> Either s a) -> (a -> s) -> Prism a s
mkPrism m b = 
  ex2prof @Any @(->) @Any @(->) @Any @(->) @Either @Void
  $ Optic m (either id b)

-- Algebraic lenses are optics
type AlgebraicLens m a s = (Monad m) => ProfOptic Any (->) Any (->) (Algebra m) (->) (,) () (,) (,) a a s s
mkAlgebraicLens :: forall m a s . (Monad m) => (s -> a) -> (m s -> a -> s) -> AlgebraicLens m a s
mkAlgebraicLens v u =
  ex2prof @Any @(->) @Any @(->) @(Algebra m) @(->) @(,) @()
  $ Optic (\a -> (return a , v a)) (\(ms,b) -> u ms b)

type Kaleidoscope a s = ProfOptic Any (->) Any (->) Applicative Nat Compose Identity App App a a s s
mkKaleidoscope :: (([a] -> a) -> ([s] -> s)) -> Kaleidoscope a s
mkKaleidoscope f =
  ex2prof @Any @(->) @Any @(->) @Applicative @Nat @Compose @Identity @App @App
  $ Optic (App . flip More (Done id)) (uncurry (flip f) . noFun . getApp)
    where
      noFun :: FunList s a b -> ([s] , ([a] -> b))
      noFun (Done b) = ([] , const b)
      noFun (More s l) = (\(u , f) -> (s:u , \(h:t) -> f t h)) $ noFun l

type MonadicLens m a b s t = (Monad m) => ProfOptic Any (->) Any (Kleisli m) Any (->) (,) () (,) (,) a b s t
mkMonadicLens :: forall m a b s t . (Monad m) => (s -> a) -> (s -> b -> m t) -> MonadicLens m a b s t
mkMonadicLens v u =
  ex2prof @Any @(->) @Any @(Kleisli m) @Any @(->) @(,) @() @(,) @(,)
  $ Optic (\a -> (a , v a)) (Kleisli (uncurry u))

-- Traversals as optics for the action of traversable functors.
type Traversal a s = ProfOptic Any (->) Any (->) Traversable Nat Compose Identity App App a a s s
mkTraversal :: forall a b s t . (s -> [a]) -> ([a] -> s) -> Traversal a s
mkTraversal l r =
  ex2prof @Any @(->) @Any @(->) @Traversable @Nat @Compose @Identity @App @App
  $ Optic (App . l) (r . getApp)
