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
    happly-equiv : (f g : (x : A) → B x) → is-equiv (happly f g)

  funext : (f g : (x : A) → B x) → ((x : A) → f x == g x) -> (f == g)
  funext f g = is-equiv.g (happly-equiv f g)

  h-h-inv : (f g : (x : A) → B x) -> ( α : ((x : A) → f x == g x))
    -> (happly f g (funext f g α)) == α
  h-h-inv f g α = (is-equiv.ε (happly-equiv f g)) α

  h-inv-h : (f g : (x : A) → B x) -> (α : f == g)
    -> (funext f g (happly f g α)) == α
  h-inv-h f g α = (is-equiv.η (happly-equiv f g)) α
