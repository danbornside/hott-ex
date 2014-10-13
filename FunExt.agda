{-# OPTIONS --without-K #-}

module FunExt where

open import Base

module _ {i j} {A : Type i} {B : A → Type j} where

  happly : (f g : (x : A) → B x) → (f == g) → ((x : A) → f x == g x)
  happly f g = ind== D d where
    D : (f g : (x : A) → B x) → f == g → Type _
    D f g _ = (x : A) → f x == g x

    d : (f : (x : A) → B x) → D f f refl
    d f = λ x → refl

  postulate
    fun-ext : (f g : (x : A) → B x) → is-equiv (happly f g)
