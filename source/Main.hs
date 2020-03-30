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

module Main where

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
import Optics
import Combinators

-- EXAMPLE 1: Lenses and prisms.
data Address = Address
  { street'  :: String
  , city'    :: String
  , country' :: String
  } deriving (Show)

home :: String
home = "221b Baker St, London, UK"

street :: Lens String Address
street = mkLens street' (\x y -> x {street' = y})

city :: Lens String Address
city = mkLens city' (\x y -> x {city' = y})

address :: Prism Address String
address = mkPrism matchPostal buildPostal
  where
    matchPostal :: String -> Either String Address 
    matchPostal a = maybe (Left a) Right $ do
      (street, b) <- readUntil ',' a
      (city, c)   <- readUntil ',' (tail $ tail b)
      return $ Address street city (tail $ tail c)
    buildPostal :: Address -> String
    buildPostal (Address s t c) = s ++ ", " ++ t ++ ", " ++ c

    readUntil :: Char -> String -> Maybe (String , String)
    readUntil c a = if elem c a
      then Just (takeWhile (/= c) a, dropWhile (/= c) a)
      else Nothing


-- EXAMPLE 2: Kaleidoscope and algebraic lenses
data Species = None | Setosa | Versicolor | Virginica | Mixed

data Measurements = Measurements
  { sepalLe :: Float
  , sepalWi :: Float
  , petalLe :: Float
  , petalWi :: Float
  }

data Flower = Flower
  { measurements :: Measurements
  , species      :: Species
  }

instance Show Flower where
  show (Flower m s) = show s ++ " " ++ show m

instance Show Species where
  show None       = "No Species"
  show Setosa     = "Iris Setosa"
  show Versicolor = "Iris Versicolor"
  show Virginica  = "Iris Virginica"

instance Show Measurements where
  show (Measurements sl sw pl pw) =
    "(" ++ show sl ++ ", " ++ show sw ++ ", " 
        ++ show pl ++ ", " ++ show pw ++ ")"


measure :: AlgebraicLens [] Measurements Flower
measure = mkAlgebraicLens @[] measurements learn
  where
    distance :: Measurements -> Measurements -> Float
    distance (Measurements a b c d) (Measurements x y z w) =
      sqrt . sum . fmap (**2) $ [a-x,b-y,c-z,d-w]

    learn :: [Flower] -> Measurements -> Flower
    learn l m = Flower m $
      species (minimumBy (compare `on` (distance m . measurements)) l)

aggregate :: Kaleidoscope Float Measurements
aggregate = mkKaleidoscope $ \f l -> Measurements
  (f $ fmap sepalLe l)
  (f $ fmap sepalWi l)
  (f $ fmap petalLe l)
  (f $ fmap petalWi l)
    
mean :: [Float] -> Float
mean l = (sum l) / (fromIntegral $ length l)

iris :: [Flower]
iris = [
  Flower (Measurements 5.1 3.5 1.4 0.2) Setosa,
  Flower (Measurements 4.9 3.0 1.4 0.2) Setosa,
  Flower (Measurements 4.7 3.2 1.3 0.2) Setosa,
  Flower (Measurements 4.6 3.1 1.5 0.2) Setosa,
  Flower (Measurements 5.0 3.6 1.4 0.2) Setosa,
  Flower (Measurements 5.4 3.9 1.7 0.4) Setosa,
  Flower (Measurements 4.6 3.4 1.4 0.3) Setosa,
  Flower (Measurements 5.0 3.4 1.5 0.2) Setosa,
  Flower (Measurements 4.4 2.9 1.4 0.2) Setosa,
  Flower (Measurements 4.9 3.1 1.5 0.1) Setosa,
  Flower (Measurements 5.4 3.7 1.5 0.2) Setosa,
  Flower (Measurements 4.8 3.4 1.6 0.2) Setosa,
  Flower (Measurements 4.8 3.0 1.4 0.1) Setosa,
  Flower (Measurements 4.3 3.0 1.1 0.1) Setosa,
  Flower (Measurements 5.8 4.0 1.2 0.2) Setosa,
  Flower (Measurements 5.7 4.4 1.5 0.4) Setosa,
  Flower (Measurements 5.4 3.9 1.3 0.4) Setosa,
  Flower (Measurements 5.1 3.5 1.4 0.3) Setosa,
  Flower (Measurements 5.7 3.8 1.7 0.3) Setosa,
  Flower (Measurements 5.1 3.8 1.5 0.3) Setosa,
  Flower (Measurements 5.4 3.4 1.7 0.2) Setosa,
  Flower (Measurements 5.1 3.7 1.5 0.4) Setosa,
  Flower (Measurements 4.6 3.6 1.0 0.2) Setosa,
  Flower (Measurements 5.1 3.3 1.7 0.5) Setosa,
  Flower (Measurements 4.8 3.4 1.9 0.2) Setosa,
  Flower (Measurements 5.0 3.0 1.6 0.2) Setosa,
  Flower (Measurements 5.0 3.4 1.6 0.4) Setosa,
  Flower (Measurements 5.2 3.5 1.5 0.2) Setosa,
  Flower (Measurements 5.2 3.4 1.4 0.2) Setosa,
  Flower (Measurements 4.7 3.2 1.6 0.2) Setosa,
  Flower (Measurements 4.8 3.1 1.6 0.2) Setosa,
  Flower (Measurements 5.4 3.4 1.5 0.4) Setosa,
  Flower (Measurements 5.2 4.1 1.5 0.1) Setosa,
  Flower (Measurements 5.5 4.2 1.4 0.2) Setosa,
  Flower (Measurements 4.9 3.1 1.5 0.1) Setosa,
  Flower (Measurements 5.0 3.2 1.2 0.2) Setosa,
  Flower (Measurements 5.5 3.5 1.3 0.2) Setosa,
  Flower (Measurements 4.9 3.1 1.5 0.1) Setosa,
  Flower (Measurements 4.4 3.0 1.3 0.2) Setosa,
  Flower (Measurements 5.1 3.4 1.5 0.2) Setosa,
  Flower (Measurements 5.0 3.5 1.3 0.3) Setosa,
  Flower (Measurements 4.5 2.3 1.3 0.3) Setosa,
  Flower (Measurements 4.4 3.2 1.3 0.2) Setosa,
  Flower (Measurements 5.0 3.5 1.6 0.6) Setosa,
  Flower (Measurements 5.1 3.8 1.9 0.4) Setosa,
  Flower (Measurements 4.8 3.0 1.4 0.3) Setosa,
  Flower (Measurements 5.1 3.8 1.6 0.2) Setosa,
  Flower (Measurements 4.6 3.2 1.4 0.2) Setosa,
  Flower (Measurements 5.3 3.7 1.5 0.2) Setosa,
  Flower (Measurements 5.0 3.3 1.4 0.2) Setosa,
  Flower (Measurements 7.0 3.2 4.7 1.4) Versicolor,
  Flower (Measurements 6.4 3.2 4.5 1.5) Versicolor,
  Flower (Measurements 6.9 3.1 4.9 1.5) Versicolor,
  Flower (Measurements 5.5 2.3 4.0 1.3) Versicolor,
  Flower (Measurements 6.5 2.8 4.6 1.5) Versicolor,
  Flower (Measurements 5.7 2.8 4.5 1.3) Versicolor,
  Flower (Measurements 6.3 3.3 4.7 1.6) Versicolor,
  Flower (Measurements 4.9 2.4 3.3 1.0) Versicolor,
  Flower (Measurements 6.6 2.9 4.6 1.3) Versicolor,
  Flower (Measurements 5.2 2.7 3.9 1.4) Versicolor,
  Flower (Measurements 5.0 2.0 3.5 1.0) Versicolor,
  Flower (Measurements 5.9 3.0 4.2 1.5) Versicolor,
  Flower (Measurements 6.0 2.2 4.0 1.0) Versicolor,
  Flower (Measurements 6.1 2.9 4.7 1.4) Versicolor,
  Flower (Measurements 5.6 2.9 3.6 1.3) Versicolor,
  Flower (Measurements 6.7 3.1 4.4 1.4) Versicolor,
  Flower (Measurements 5.6 3.0 4.5 1.5) Versicolor,
  Flower (Measurements 5.8 2.7 4.1 1.0) Versicolor,
  Flower (Measurements 6.2 2.2 4.5 1.5) Versicolor,
  Flower (Measurements 5.6 2.5 3.9 1.1) Versicolor,
  Flower (Measurements 5.9 3.2 4.8 1.8) Versicolor,
  Flower (Measurements 6.1 2.8 4.0 1.3) Versicolor,
  Flower (Measurements 6.3 2.5 4.9 1.5) Versicolor,
  Flower (Measurements 6.1 2.8 4.7 1.2) Versicolor,
  Flower (Measurements 6.4 2.9 4.3 1.3) Versicolor,
  Flower (Measurements 6.6 3.0 4.4 1.4) Versicolor,
  Flower (Measurements 6.8 2.8 4.8 1.4) Versicolor,
  Flower (Measurements 6.7 3.0 5.0 1.7) Versicolor,
  Flower (Measurements 6.0 2.9 4.5 1.5) Versicolor,
  Flower (Measurements 5.7 2.6 3.5 1.0) Versicolor,
  Flower (Measurements 5.5 2.4 3.8 1.1) Versicolor,
  Flower (Measurements 5.5 2.4 3.7 1.0) Versicolor,
  Flower (Measurements 5.8 2.7 3.9 1.2) Versicolor,
  Flower (Measurements 6.0 2.7 5.1 1.6) Versicolor,
  Flower (Measurements 5.4 3.0 4.5 1.5) Versicolor,
  Flower (Measurements 6.0 3.4 4.5 1.6) Versicolor,
  Flower (Measurements 6.7 3.1 4.7 1.5) Versicolor,
  Flower (Measurements 6.3 2.3 4.4 1.3) Versicolor,
  Flower (Measurements 5.6 3.0 4.1 1.3) Versicolor,
  Flower (Measurements 5.5 2.5 4.0 1.3) Versicolor,
  Flower (Measurements 5.5 2.6 4.4 1.2) Versicolor,
  Flower (Measurements 6.1 3.0 4.6 1.4) Versicolor,
  Flower (Measurements 5.8 2.6 4.0 1.2) Versicolor,
  Flower (Measurements 5.0 2.3 3.3 1.0) Versicolor,
  Flower (Measurements 5.6 2.7 4.2 1.3) Versicolor,
  Flower (Measurements 5.7 3.0 4.2 1.2) Versicolor,
  Flower (Measurements 5.7 2.9 4.2 1.3) Versicolor,
  Flower (Measurements 6.2 2.9 4.3 1.3) Versicolor,
  Flower (Measurements 5.1 2.5 3.0 1.1) Versicolor,
  Flower (Measurements 5.7 2.8 4.1 1.3) Versicolor,
  Flower (Measurements 6.3 3.3 6.0 2.5) Virginica,
  Flower (Measurements 5.8 2.7 5.1 1.9) Virginica,
  Flower (Measurements 7.1 3.0 5.9 2.1) Virginica,
  Flower (Measurements 6.3 2.9 5.6 1.8) Virginica,
  Flower (Measurements 6.5 3.0 5.8 2.2) Virginica,
  Flower (Measurements 7.6 3.0 6.6 2.1) Virginica,
  Flower (Measurements 4.9 2.5 4.5 1.7) Virginica,
  Flower (Measurements 7.3 2.9 6.3 1.8) Virginica,
  Flower (Measurements 6.7 2.5 5.8 1.8) Virginica,
  Flower (Measurements 7.2 3.6 6.1 2.5) Virginica,
  Flower (Measurements 6.5 3.2 5.1 2.0) Virginica,
  Flower (Measurements 6.4 2.7 5.3 1.9) Virginica,
  Flower (Measurements 6.8 3.0 5.5 2.1) Virginica,
  Flower (Measurements 5.7 2.5 5.0 2.0) Virginica,
  Flower (Measurements 5.8 2.8 5.1 2.4) Virginica,
  Flower (Measurements 6.4 3.2 5.3 2.3) Virginica,
  Flower (Measurements 6.5 3.0 5.5 1.8) Virginica,
  Flower (Measurements 7.7 3.8 6.7 2.2) Virginica,
  Flower (Measurements 7.7 2.6 6.9 2.3) Virginica,
  Flower (Measurements 6.0 2.2 5.0 1.5) Virginica,
  Flower (Measurements 6.9 3.2 5.7 2.3) Virginica,
  Flower (Measurements 5.6 2.8 4.9 2.0) Virginica,
  Flower (Measurements 7.7 2.8 6.7 2.0) Virginica,
  Flower (Measurements 6.3 2.7 4.9 1.8) Virginica,
  Flower (Measurements 6.7 3.3 5.7 2.1) Virginica,
  Flower (Measurements 7.2 3.2 6.0 1.8) Virginica,
  Flower (Measurements 6.2 2.8 4.8 1.8) Virginica,
  Flower (Measurements 6.1 3.0 4.9 1.8) Virginica,
  Flower (Measurements 6.4 2.8 5.6 2.1) Virginica,
  Flower (Measurements 7.2 3.0 5.8 1.6) Virginica,
  Flower (Measurements 7.4 2.8 6.1 1.9) Virginica,
  Flower (Measurements 7.9 3.8 6.4 2.0) Virginica,
  Flower (Measurements 6.4 2.8 5.6 2.2) Virginica,
  Flower (Measurements 6.3 2.8 5.1 1.5) Virginica,
  Flower (Measurements 6.1 2.6 5.6 1.4) Virginica,
  Flower (Measurements 7.7 3.0 6.1 2.3) Virginica,
  Flower (Measurements 6.3 3.4 5.6 2.4) Virginica,
  Flower (Measurements 6.4 3.1 5.5 1.8) Virginica,
  Flower (Measurements 6.0 3.0 4.8 1.8) Virginica,
  Flower (Measurements 6.9 3.1 5.4 2.1) Virginica,
  Flower (Measurements 6.7 3.1 5.6 2.4) Virginica,
  Flower (Measurements 6.9 3.1 5.1 2.3) Virginica,
  Flower (Measurements 5.8 2.7 5.1 1.9) Virginica,
  Flower (Measurements 6.8 3.2 5.9 2.3) Virginica,
  Flower (Measurements 6.7 3.3 5.7 2.5) Virginica,
  Flower (Measurements 6.7 3.0 5.2 2.3) Virginica,
  Flower (Measurements 6.3 2.5 5.0 1.9) Virginica,
  Flower (Measurements 6.5 3.0 5.2 2.0) Virginica,
  Flower (Measurements 6.2 3.4 5.4 2.3) Virginica,
  Flower (Measurements 5.9 3.0 5.1 1.8) Virginica]


-- EXAMPLE 3: Updating with monadic lenses.
newtype Box a = Box { openBox :: a }

instance Show a => Show (Box a) where
  show (Box a) = "Box{" ++ show a ++ "}"

box :: (Show b) => MonadicLens IO a b (Box a) (Box b)
box = mkMonadicLens @IO openBox $ \ u b -> do
  putStrLn $ "[box]: contents changed to " ++ show b ++ "."
  return $ Box b

-- EXAMPLE 4: Traversals
each :: Traversal a [a]
each = mkTraversal id id

uppercase :: String -> String
uppercase = fmap toUpper

mail :: [String]
mail =
 [ "43 Adlington Rd, Wilmslow, United Kingdom"
 , "26 Westcott Rd, Princeton, USA"
 , "St James's Square, London, United Kingdom"
 ]


-- Main
main :: IO ()
main = return ()
