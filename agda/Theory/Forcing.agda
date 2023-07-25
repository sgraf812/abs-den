{-# OPTIONS --cubical --guarded --rewriting #-}

open import Utils.Later
open import Utils.PartialFunction
open import Utils.Addrs
open import Syntax hiding (Val)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.List as L
open import Data.Maybe
open import Data.Product
open import Function
open import Cubical.Relation.Nullary

module Theory.Forcing (as : Addrs) where
open Addrs as
import Semantics.Eventful
open module Sem = Semantics.Eventful as


