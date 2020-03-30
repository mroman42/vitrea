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
Module      : Categories
Description : Constrained categories
Copyright   : (c) Mario Román, 2020
License     : GPL-3
Maintainer  : mromang08@gmail.com
Stability   : experimental
Portability : POSIX

Provides a definition of category enriched over Hask, where the sets of objects
are represented by constraints.  Considers also functors and monoidal categories.
-}


module Categories where

-- | Definition of a category enriched over the language. The sets of objects
-- are represented by constraints.
class Category objc c where
  unit :: (objc x) => c x x                        
  comp :: (objc x) => c y z -> c x y -> c x z

-- | Functors.
class ( Category objc c, Category objd d
      , forall x . objc x => objd (f x)
      ) => VFunctor objc c objd d f where
  map :: (objc x, objc y) => c x y -> d (f x) (f y)

-- | Bifunctors.
class ( Category objc c, Category objd d, Category obje e
      , forall x y . (objc x , objd y) => obje (f x y) )
      => Bifunctor objc c objd d obje e f where
  bimap :: ( objc x1, objc x2, objd y1, objd y2 )
        => c x1 x2 -> d y1 y2 -> e (f x1 y1) (f x2 y2)

-- | Profunctors.
class ( Category objc c, Category objd d )
      => Profunctor objc c objd d p where
  dimap :: (objc x1, objc x2, objd y1, objd y2)
        => c x2 x1 -> d y1 y2 -> p x1 y1 -> p x2 y2

-- | Monoidal categories. The definition follows that of an enriched monoidal
-- category, taking the language as the base of enrichment.
class ( Category obja a
      , Bifunctor obja a obja a obja a o
      , obja i )
      => MonoidalCategory obja a o i where
  alpha  :: (obja x, obja y, obja z) 
         => a (x `o` (y `o` z)) ((x `o` y) `o` z)
  alphainv  :: (obja x, obja y, obja z)
            => a ((x `o` y) `o` z) (x `o` (y `o` z))
  lambda    :: (obja x) => a (x `o` i) x
  lambdainv :: (obja x) => a x (x `o` i)
  rho       :: (obja x) => a (i `o` x) x
  rhoinv    :: (obja x) => a x (i `o` x)

-- | Monoidal actions as suitable bifunctors with the corresponding structure
-- maps.
class ( MonoidalCategory objm m o i
      , Bifunctor objm m objc c objc c f
      , Category objc c )
      => MonoidalAction objm m o i objc c f where
  unitor :: (objc x) => c (f i x) x
  unitorinv :: (objc x) => c x (f i x)
  multiplicator :: (objc x, objm p, objm q)
                => c (f p (f q x)) (f (p `o` q) x) 
  multiplicatorinv :: (objc x, objm p, objm q)
                => c (f (p `o` q) x) (f p (f q x)) 
