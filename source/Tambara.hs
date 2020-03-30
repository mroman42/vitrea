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
Module      : Tambara
Description : Generalized Tambara modules
Copyright   : (c) Mario Román, 2020
License     : GPL-3
Maintainer  : mromang08@gmail.com
Stability   : experimental
Portability : POSIX

Presents the unified definition of optic and generalized Tambara modules. This
definition has been studied by Milewski ("Profunctor optics, the categorical
view", 2016), then by Boisseau and Gibbons ("What you needa know about Yoneda",
2017), then by Riley ("Categories of optics", 2018), and in the mixed enriched
case we implement by Clarke, Elkins, Gibbons, Loregian, Milewski, Pillmore and
Román ("Profunctor optics, a categorical update", 2019).
-}


module Tambara where

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

-- | Unified definition of a mixed optic, enriched over Hask (from "Profunctor
-- optics, a categorical update", Definition 2.1).
data Optic objc c objd d objm m o i f g a b s t where
  Optic :: ( MonoidalAction objm m o i objc c f
           , MonoidalAction objm m o i objd d g
           , objc a, objc s , objd b, objd t , objm x )
        => c s (f x a) -> d (g x b) t
        -> Optic objc c objd d objm m o i f g a b s t

-- | Generalized Tambara modules for a pair of monoidal actions on possibly
-- different categories.
class ( MonoidalAction objm m o i objc c f
      , MonoidalAction objm m o i objd d g
      , Profunctor objc c objd d p )
      => Tambara objc c objd d objm m o i f g p where
  tambara :: (objc x, objd y, objm w)
          => p x y -> p (f w x) (g w y)

-- | Unified definition of Profunctor optic in terms of Tambara modules. This is
-- the Yoneda representation of the category of optics, with Tambara modules as
-- copresheaves.
type ProfOptic objc c objd d objm m o i f g a b s t = forall p .
  ( Tambara objc c objd d objm m o i f g p
  , MonoidalAction objm m o i objc c f
  , MonoidalAction objm m o i objd d g
  , objc a , objd b , objc s , objd t
  ) => p a b -> p s t

instance ( MonoidalAction objm m o i objc c f
         , MonoidalAction objm m o i objd d g
         , objc a , objd b )
         => Profunctor objc c objd d (Optic objc c objd d objm m o i f g a b) where
  dimap f g (Optic l r) = Optic (comp @objc @c l f) (comp @objd @d g r)

instance ( MonoidalAction objm m o i objc c f
         , MonoidalAction objm m o i objd d g
         , objc a , objd b )
         => Tambara objc c objd d objm m o i f g (Optic objc c objd d objm m o i f g a b) where
  tambara (Optic l r) = Optic
    (comp @objc @c (multiplicator @objm @m @o @i @objc @c @f) (bimap @objm @m @objc @c @objc @c (unit @objm @m) l))
    (comp @objd @d (bimap @objm @m @objd @d @objd @d (unit @objm @m) r) (multiplicatorinv @objm @m @o @i @objd @d @g))

-- | Transforms an existential optic into its profunctor representation. This is
-- one side of a Yoneda embedding.
ex2prof :: forall objc c objd d objm m o i f g a b s t .
       Optic     objc c objd d objm m o i f g a b s t 
    -> ProfOptic objc c objd d objm m o i f g a b s t
ex2prof (Optic l r) =
  dimap @objc @c @objd @d l r .
  tambara @objc @c @objd @d @objm @m @o @i

-- | Transforms a profunctor optic into its existential representation. This is
-- the other side of a Yoneda embedding.
prof2ex :: forall objc c objd d objm m o i f g a b s t .
    ( MonoidalAction objm m o i objc c f
    , MonoidalAction objm m o i objd d g
    , objc a , objc s
    , objd b , objd t )
    => ProfOptic objc c objd d objm m o i f g a b s t 
    -> Optic     objc c objd d objm m o i f g a b s t
prof2ex p = p (Optic
    (unitorinv @objm @m @o @i @objc @c @f) 
    (unitor @objm @m @o @i @objd @d @g))
