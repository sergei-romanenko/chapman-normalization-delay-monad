module BasicSystem.Utils where

open import Agda.Primitive public
open import Size public
  hiding (↑_)
open import Category.Monad public
  using (RawMonad; module RawMonad)

open import Data.Unit using (⊤; tt) public
open import Data.Product public

open import Function public

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_]) public

open import Relation.Binary
  using (Setoid) public
