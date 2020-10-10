{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Vec where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (Maybe)
private
  variable
    a : Level
    A B : Set a
    n : Nat
infixr 5 _∷_
postulate Vec : (A : Set a) → Nat → Set a
primitive
   primVectorCons  : A → Vec A n → Vec A (suc n)
   primVectorEmpty : A → Vec A zero
   primVectorHead  : Vec A (suc n) → A
   primVectorTail  : Vec A (suc n) → Vec A n
   primVectorIndex : (n : Nat) → Vec A (suc n) → A
   primVectorSafeIndex : (n : Nat) → Vec A n → Maybe A
   primVectorReverse : Vec A n → Vec A n
   primVectorSnoc : Vec A n → A → Vec A (suc n)
   primVectorFoldr : (A → B → B) → B → Vec A n → B

{-# BUILTIN VECTOR Vec #-}
