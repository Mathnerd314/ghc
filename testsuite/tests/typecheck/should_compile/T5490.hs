{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Bug where

import Data.Typeable
import Data.Functor
import Control.Exception

data Attempt α = Success α
               | ∀ e . Exception e ⇒ Failure e 

data NthException n e = NthException (Peano n) e deriving (Typeable, Show)

instance (Typeable n, Exception e) ⇒ Exception (NthException n e)

inj n (Success r) = Success (HNth n r)
inj n (Failure e) = Failure (NthException n e)

data PZero deriving Typeable
data PSucc p deriving Typeable

data Peano n where
  PZero ∷ Peano PZero
  PSucc ∷ IsPeano p ⇒ Peano p → Peano (PSucc p)

instance Show (Peano n) where
  show n = show (peanoNum n ∷ Int)

peanoNum ∷ Num n ⇒ Peano p → n
peanoNum = undefined

class Typeable n ⇒ IsPeano n where
  peano ∷ Peano n

instance IsPeano PZero where
  peano = PZero

instance IsPeano p ⇒ IsPeano (PSucc p) where
  peano = PSucc peano 

infixr 7 :*
infix  8 :*:

data HNil
data h :* t
type HSingle α = α :* HNil
type α :*: β = α :* β :* HNil

data HList l where
  HNil ∷ HList HNil
  (:*) ∷ HListClass t ⇒ h → HList t → HList (h :* t)

data HListWitness l where
  HNilList  ∷ HListWitness HNil
  HConsList ∷ HListClass t ⇒ HListWitness (h :* t)

class HListClass l where
  hListWitness ∷ HListWitness l

instance HListClass HNil where
  hListWitness = HNilList

instance HListClass t ⇒ HListClass (h :* t) where
  hListWitness = HConsList

class (l ~ (HHead l :* HTail l), HListClass (HTail l)) ⇒ HNonEmpty l where
  type HHead l
  type HTail l

instance HListClass t ⇒ HNonEmpty (h :* t) where
  type HHead (h :* t) = h
  type HTail (h :* t) = t

data HDropWitness n l where
  HDropZero ∷ HListClass l ⇒ HDropWitness PZero l
  HDropSucc ∷ HDropClass p t ⇒ HDropWitness (PSucc p) (h :* t)

class (IsPeano n, HListClass l, HListClass (HDrop n l)) ⇒ HDropClass n l where
  type HDrop n l

instance HListClass l ⇒ HDropClass PZero l where
  type HDrop PZero l = l

instance HDropClass p t ⇒ HDropClass (PSucc p) (h :* t) where
  type HDrop (PSucc p) (h :* t) = HDrop p t

type HNth n l = HHead (HDrop n l)

data HElemOf l where
  HNth ∷ (HDropClass n l, HNonEmpty (HDrop n l))
       ⇒ Peano n → HNth n l → HElemOf l
