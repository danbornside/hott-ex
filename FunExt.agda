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

  happly-inv : (f g : (x : A) → B x) → ((x : A) → f x == g x) -> (f == g)
  happly-inv f g = is-equiv.g (fun-ext f g)

  h-h-inv : (f g : (x : A) → B x) -> ( α : ((x : A) → f x == g x))
    -> (happly f g (happly-inv f g α)) == α
  h-h-inv f g α = (is-equiv.f-g (fun-ext f g)) α

  h-inv-h : (f g : (x : A) → B x) -> (α : f == g)
    -> (happly-inv f g (happly f g α)) == α
  h-inv-h f g α = (is-equiv.g-f (fun-ext f g)) α
