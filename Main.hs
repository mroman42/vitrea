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

import Prelude hiding (map)
import Data.Constraint
import Data.Void
import Data.Function
import Data.Either
import Control.Monad.Writer hiding (Any)
import Control.Monad
import Data.Char
import Data.List
import Data.Monoid hiding (Any)
import Text.Printf
import Data.Functor.Compose
import Data.Functor.Identity

-- Enriched category theory
class Category objc c where
  unit :: (objc x) => c x x                        
  comp :: (objc x) => c y z -> c x y -> c x z

class ( Category objc c, Category objd d
      , forall x . objc x => objd (f x)
      ) => VFunctor objc c objd d f where
  map :: (objc x, objc y) => c x y -> d (f x) (f y)

class ( Category objc c, Category objd d, Category obje e
      , forall x y . (objc x , objd y) => obje (f x y) )
      => Bifunctor objc c objd d obje e f where
  bimap :: ( objc x1, objc x2, objd y1, objd y2 )
        => c x1 x2 -> d y1 y2 -> e (f x1 y1) (f x2 y2)

class ( Category objc c, Category objd d )
      => Profunctor objc c objd d p where
  dimap :: (objc x1, objc x2, objd y1, objd y2)
        => c x2 x1 -> d y1 y2 -> p x1 y1 -> p x2 y2

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



-- Instances for some common categories
class Any x
instance Any x

instance Category Any (->) where
  unit = \x -> x
  comp = \g f x -> g (f x)

newtype Nat f g = Nat { nat :: forall x . f x -> g x }

instance Category Functor Nat where
  unit = Nat id
  comp (Nat h) (Nat k) = Nat (h . k)

instance Category Applicative Nat where
  unit = unit @Functor
  comp = comp @Functor

instance Category Traversable Nat where
  unit = unit @Functor
  comp = comp @Functor

newtype App f a = App { getApp :: f a }

instance Bifunctor Any (->) Any (->) Any (->) (,) where
  bimap f g (x,y) = (f x , g y)

instance Bifunctor Functor Nat Functor Nat Functor Nat Compose where
  bimap (Nat h) (Nat k) = Nat (Compose . fmap k . h . getCompose)

instance Bifunctor Applicative Nat Applicative Nat Applicative Nat Compose where
  bimap = bimap @Functor @Nat @Functor @Nat @Functor @Nat @Compose

instance Bifunctor Traversable Nat Traversable Nat Traversable Nat Compose where
  bimap = bimap @Functor @Nat @Functor @Nat @Functor @Nat @Compose


instance Bifunctor Any (->) Any (->) Any (->) Either where
  bimap f _ (Left x)  = Left  (f x)
  bimap _ g (Right x) = Right (g x)

instance Bifunctor Functor Nat Any (->) Any (->) App where
  bimap (Nat h) f = App . fmap f . h . getApp
instance Bifunctor Applicative Nat Any (->) Any (->) App where
  bimap = bimap @Functor @Nat @Any @(->) @Any @(->) @App
instance Bifunctor Traversable Nat Any (->) Any (->) App where
  bimap = bimap @Functor @Nat @Any @(->) @Any @(->) @App


instance MonoidalCategory Any (->) (,) () where
  alpha (x,(y,z)) = ((x,y),z)
  alphainv ((x,y),z) = (x,(y,z))
  lambda (x,_) = x
  lambdainv x = (x,())
  rho (_,x) = x
  rhoinv x = ((),x)

instance MonoidalCategory Any (->) Either Void where
  alpha = either (Left . Left) (either (Left . Right) Right)
  alphainv = either (either Left (Right . Left)) (Right . Right)
  lambda = either (\x -> x) absurd
  lambdainv = Left
  rho = either absurd (\x -> x)
  rhoinv = Right

instance MonoidalCategory Functor Nat Compose Identity where
  alpha = Nat (Compose . Compose . fmap getCompose . getCompose)
  alphainv = Nat (Compose . fmap Compose . getCompose . getCompose)
  lambda = Nat (fmap runIdentity . getCompose)
  lambdainv = Nat (Compose . fmap Identity)
  rho = Nat (runIdentity . getCompose)
  rhoinv = Nat (Compose . Identity)

instance MonoidalCategory Applicative Nat Compose Identity where
  alpha = alpha @Functor @Nat @Compose @Identity
  alphainv = alphainv @Functor @Nat @Compose @Identity
  lambda = lambda @Functor @Nat @Compose @Identity
  lambdainv = lambdainv @Functor @Nat @Compose @Identity
  rho = rho @Functor @Nat @Compose @Identity
  rhoinv = rhoinv @Functor @Nat @Compose @Identity

instance MonoidalCategory Traversable Nat Compose Identity where
  alpha = alpha @Functor @Nat @Compose @Identity
  alphainv = alphainv @Functor @Nat @Compose @Identity
  lambda = lambda @Functor @Nat @Compose @Identity
  lambdainv = lambdainv @Functor @Nat @Compose @Identity
  rho = rho @Functor @Nat @Compose @Identity
  rhoinv = rhoinv @Functor @Nat @Compose @Identity

instance MonoidalAction Functor Nat Compose Identity Any (->) App where
  unitor = runIdentity . getApp
  unitorinv = App . Identity
  multiplicator = App . Compose . fmap getApp . getApp
  multiplicatorinv = App . fmap App . getCompose . getApp

instance MonoidalAction Applicative Nat Compose Identity Any (->) App where
  unitor = unitor @Functor @Nat @Compose @Identity @Any @(->) @App
  unitorinv = unitorinv @Functor @Nat @Compose @Identity @Any @(->) @App
  multiplicator = multiplicator @Functor @Nat @Compose @Identity @Any @(->) @App
  multiplicatorinv = multiplicatorinv @Functor @Nat @Compose @Identity @Any @(->) @App

instance MonoidalAction Traversable Nat Compose Identity Any (->) App where
  unitor = unitor @Functor @Nat @Compose @Identity @Any @(->) @App
  unitorinv = unitorinv @Functor @Nat @Compose @Identity @Any @(->) @App
  multiplicator = multiplicator @Functor @Nat @Compose @Identity @Any @(->) @App
  multiplicatorinv = multiplicatorinv @Functor @Nat @Compose @Identity @Any @(->) @App

instance (MonoidalCategory objm m o i) => MonoidalAction objm m o i objm m o where
  unitor = rho @objm @m
  unitorinv = rhoinv @objm @m
  multiplicator = alpha @objm @m @o @i
  multiplicatorinv = alphainv @objm @m @o @i
  

class (Monad m) => Algebra m a where
  algebra :: m a -> a

instance (Monad m) => Algebra m (m a) where
  algebra = join

instance (Monad m) => Category (Algebra m) (->) where
  unit = unit @Any
  comp = comp @Any

instance (Monad m) => Bifunctor (Algebra m) (->) (Algebra m) (->) (Algebra m) (->) (,) where
  bimap = bimap @Any @(->) @Any @(->) @Any @(->)

instance (Monad m) => Algebra m () where
  algebra _ = ()

instance (Monad m, Algebra m x, Algebra m y) => Algebra m (x,y) where
  algebra u = (algebra $ fmap fst u, algebra $ fmap snd u)

instance (Monad m) => MonoidalCategory (Algebra m) (->) (,) () where
  alpha     = alpha     @Any @(->) @(,) @()
  alphainv  = alphainv  @Any @(->) @(,) @()
  lambda    = lambda    @Any @(->) @(,) @()
  lambdainv = lambdainv @Any @(->) @(,) @()
  rho       = rho       @Any @(->) @(,) @()
  rhoinv    = rhoinv    @Any @(->) @(,) @()

instance (Monad m) => Bifunctor (Algebra m) (->) Any (->) Any (->) (,) where
  bimap = bimap @Any @(->) @Any @(->) @Any @(->) @(,)

instance (Monad m) => MonoidalAction (Algebra m) (->) (,) () Any (->) (,) where
  unitor           = unitor           @Any @(->) @(,) @() @Any @(->) @(,)
  unitorinv        = unitorinv        @Any @(->) @(,) @() @Any @(->) @(,)
  multiplicator    = multiplicator    @Any @(->) @(,) @() @Any @(->) @(,)
  multiplicatorinv = multiplicatorinv @Any @(->) @(,) @() @Any @(->) @(,)

-- FunLists are the free applicatives over Store functors. We
-- implement the type-changing FunList.
data FunList s a b = Done b | More s (FunList s a (a -> b))

instance Functor (FunList s a) where
  fmap f (Done b) = Done (f b)
  fmap f (More s l) = More s (fmap (f .) l)

-- This instance declaration can be seen, for instance, in Pickering,
-- Gibbons, Wu.
instance Applicative (FunList s a) where
  pure = Done
  (Done f) <*> l' = fmap f l'
  (More x l) <*> l' = More x (fmap flip l <*> l')

-- Kleisli categories of free algebras.  The morphisms Kl(a,b) are
-- written in the usual (a -> m b) form.
newtype Kleisli m a b = Kleisli { getKleisli :: (a -> m b) }

instance (Monad m) => Category Any (Kleisli m) where
  unit = Kleisli return
  comp (Kleisli g) (Kleisli f) = Kleisli (join . fmap g . f)

instance (Monad m) => Bifunctor Any (->) Any (Kleisli m) Any (Kleisli m) (,) where
  bimap f (Kleisli g) = Kleisli (\(x,y) -> fmap ((,) (f x)) (g y))

instance (Monad m) => MonoidalAction Any (->) (,) () Any (Kleisli m) (,) where
  unitor = unitor @Any @(->) @(,) @() @Any @(Kleisli m) @(,)
  unitorinv = unitorinv @Any @(->) @(,) @() @Any @(Kleisli m) @(,)
  multiplicator = multiplicator @Any @(->) @(,) @() @Any @(Kleisli m) @(,)
  multiplicatorinv = multiplicatorinv @Any @(->) @(,) @() @Any @(Kleisli m) @(,)


-- OPTICS 

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
  

-- COMBINATORS

-- The class of profunctors that admit the 'view' operator.
newtype Viewing a b s t = Viewing { getView :: s -> a }
instance Profunctor Any (->) Any (->) (Viewing a b) where
  dimap l _ (Viewing f) = Viewing (f . l)

instance Tambara Any (->) Any (->) Any (->) (,) () (,) (,) (Viewing a b) where
  tambara (Viewing f) = Viewing (f . snd)

instance (Monad m) => Tambara Any (->) Any (->) (Algebra m) (->) (,) () (,) (,) (Viewing a b) where
  tambara = tambara @Any @(->) @Any @(->) @Any @(->) @(,) @()

-- The class of profunctors that admit the 'preview' operator.
newtype Previewing a b s t = Previewing { getPreview :: s -> Maybe a }
instance Profunctor Any (->) Any (->) (Previewing a b) where
  dimap l _ (Previewing f) = Previewing (f . l)

instance Tambara Any (->) Any (->) Any (->) (,) () (,) (,) (Previewing a b) where
  tambara (Previewing f) = Previewing (f . snd)

instance Tambara Any (->) Any (->) Any (->) Either Void Either Either (Previewing a b) where
  tambara (Previewing f) = Previewing (either (\_ -> Nothing) f)

-- The class of profunctors that admit the 'set' operator.
newtype Setting a b s t = Setting { getSet :: (a -> b) -> (s -> t) }
instance Profunctor Any (->) Any (->) (Setting a b) where
  dimap l r (Setting f) = Setting (\u -> r . f u . l)

instance Tambara Any (->) Any (->) Any (->) (,) () (,) (,) (Setting a b) where
  tambara (Setting f) = Setting (\u (w,x) -> (w , f u x))

instance Tambara Any (->) Any (->) Any (->) Either Void Either Either (Setting a b) where
  tambara (Setting f) = Setting (\u -> either Left (Right . f u))

-- The class of profunctors that admit the 'classify' operator.
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


-- Inspired by the "view" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 ^.
(^.) :: s -> (Viewing a b a b -> Viewing a b s t) -> a
(^.) s l = getView (l $ Viewing id) s

-- Inspired by the "preview" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 ?.
(?.) :: s -> (Previewing a b a b -> Previewing a b s t) -> Maybe a
(?.) s l = getPreview (l $ Previewing return) s

-- Inspired by the "set" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 .~
(.~) :: (Setting a b a b -> Setting a b s t) -> b -> s -> t
(.~) l b = getSet (l $ Setting id) (\_ -> b)

-- Inspired by the "over" operator of Kmett et al's lens library.  The
-- fixity and semantics are such that subsequent field accesses can be
-- performed with 'Prelude..'.
infixl 8 %~
(%~) :: (Replacing a b a b -> Replacing a b s t) -> (a -> b) -> (s -> t)
(%~) l f = getReplace (l $ Replace id) $ f

-- A "classify" operator. The fixity and semantics are such that
-- subsequent field accesses can be performed with 'Prelude..'.
infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = getClassify (l $ Classifying (\a b -> b)) ms b

-- An "aggregate" operator. The fixity and semantics are such that
-- subsequent field accesses can be performed with 'Prelude..'.
infixl 8 >-
(>-) :: (Aggregating a b a b -> Aggregating a b s t) -> ([a] -> b) -> [s] -> t
(>-) l = flip $ getAggregate (l $ Aggregate $ flip ($))

-- An "mupdate" operator. It is prepared to be used with do notation.
mupdate :: (Monad m) => (Updating m a b a b -> Updating m a b s t) -> b -> s -> m t
mupdate f = getUpdate $ f (Update (\b a -> return b))


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
