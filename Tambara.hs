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

module Tambara where

import Prelude hiding (map)
import Data.Constraint

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

-- Optics
data Optic objc c objd d objm m o i f g a b s t where
  Optic :: ( MonoidalAction objm m o i objc c f
           , MonoidalAction objm m o i objd d g
           , objc a, objc s , objd b, objd t , objm x )
        => c s (f x a) -> d (g x b) t
        -> Optic objc c objd d objm m o i f g a b s t

class ( MonoidalAction objm m o i objc c f
      , MonoidalAction objm m o i objd d g
      , Profunctor objc c objd d p )
      => Tambara objc c objd d objm m o i f g p where
  tambara :: (objc x, objd y, objm w)
          => p x y -> p (f w x) (g w y)

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

ex2prof :: forall objc c objd d objm m o i f g a b s t .
       Optic     objc c objd d objm m o i f g a b s t 
    -> ProfOptic objc c objd d objm m o i f g a b s t
ex2prof (Optic l r) =
  dimap @objc @c @objd @d l r .
  tambara @objc @c @objd @d @objm @m @o @i

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
