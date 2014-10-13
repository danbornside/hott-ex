{-# OPTIONS --without-K #-}

module Ch1 where

-- open import lib.Base
open import Base

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

-- warmup
module Eq-1-11-2 where

  -- import lib.types.Coproduct
  -- open import lib.types.Empty
  -- open import lib.types.Sigma

  -- If not A and not B, then not (A or B)
  deMorgan1 : {A B : Type0} →
    (A → ⊥) × (B → ⊥) → (Coprod A B → ⊥)
  -- deMorgan1 (notA , notB) ab = {!!} -- {!!} becomes =>
  -- deMorgan1 (notA , notB) (inl x) = {!!} -- by cases, C-c C-c on param ab
  -- deMorgan1 (notA , notB) (inr x) = {!!}
  deMorgan1 (notA , notB) (inl a) = notA a -- the 'a part' of (A + B) → ⊥
  deMorgan1 (notA , notB) (inr b) = notB b

module Ex1-1 where

  {-
Exercise 1.1. Given functions f : A -> B and g : B -> C, define their composite g o f : A ->  C.
  Show that we have h o (g o f ) == (h o g) o f
  -}

  _o_ : {A B C : Type0} → (B → C) → (A → B) → A → C
  (g o f) x = g (f x)

  o-assoc : ∀ {A B C D} →
    (h : C → D) → (g : B → C) → (f : A → B) →
    h o (g o f) == (h o g) o f
  o-assoc _ _ _ = refl -- "it's de proof"

module Ex1-2 where

  -- open import lib.types.Sigma

  -- Derive the recursion principle for products recA×B using only the projections, and
  -- verify that the definitional equalities are valid. Do the same for Σ-types.

  recAxB : {A B C : Type0} →
    (A → B → C) → A × B → C
  recAxB f ab = f (fst ab) (snd ab)

  recAxB= : ∀ {A B C}
    {f : A → B → C}
    {a : A} {b : B} →
    recAxB f (a , b) == f a b
  recAxB= = refl

  recA+B : ∀ {i j} {A : Type i} {B : Type j} {C : Type (i ⊔ j)} →
    (A → C) → (B → C) → (Coprod A B → C)
  recA+B f g (inl x) = f x
  recA+B f g (inr x) = g x

  recA+B= : {A B C : Type0}
    {f : A → C} {g : B → C}
    {a : A} {b : B} →
    (recA+B f g (inl a) == f a) × (recA+B f g (inr b) == g b)
  recA+B= = refl , refl

  recΣ : ∀ {i j} {A : Type i} {B : A → Type j} {C : Type (i ⊔ j)} →
    ((a : A) → B a → C) →
    Σ A B → C
  recΣ f ab = f (fst ab) (snd ab)

  recΣ= : ∀ {i j} {A : Type i} {B : A → Type j} {C : Type (i ⊔ j)}
    {f : (a : A) → B a → C}
    {a : A} {ba : B a} →
    recΣ f (a , ba) == f a ba
  recΣ= = refl

module Ex1-3 {i j} {A : Type i} {B : Type j} where

  -- open import lib.types.Sigma

  {- Derive the induction principle for products indA×B, using only the projections
  and the propositional uniqueness principle uppt. Verify that the definitional
  equalities are valid. Gen- eralize uppt to Σ-types, and do the same for Σ-types.
  -}

  -- book definition of uppt
  uppt-× : (x : (A × B)) → (fst x , snd x) == x
  uppt-× = λ _ → refl

  -- definition of induction principle the projections and the transported uniqueness principle
  -- (this was a confusing question to work out in Agda, since the transport is redundant)
  ind-× : (C :  (A × B) → Type (i ⊔ j)) →
    ((a : A ) → (b : B) → C (a , b)) → Π (A × B) C
  ind-× C g ab = transport C (uppt-× ab) (g (fst ab) (snd ab))

  -- (propositional) verification of defining equations
  ind-×= : (C :  (A × B) → Type (i ⊔ j)) →
    (g : ((a : A ) → (b : B) → C (a , b))) →
    ∀ {a b} → ind-× C g (a , b) == g a b
  ind-×= _ _ = refl

  -- book definition of induction principle using pattern matching
  pattern-match-ind-× : (C :  (A × B) → Type (i ⊔ j)) →
    Π A (λ x → Π B (λ y → C (x , y))) → Π (A × B) C
  pattern-match-ind-× _ g (a , b) = g a b

  -- alternative definition of uniqueness principle (from induction principle)
  ind-uppt-× : (x : (A × B)) → (fst x , snd x) == x
  ind-uppt-× = ind-× (λ z → z == z) (λ x x₁ → refl)

  -- validate definition for uppt
  uppt-×= : {x : (A × B)} → (uppt-× x) == (ind-uppt-× x)
  uppt-×= = refl

  -- uppt for Σ types
  upptΣ : {B : (a : A) → Type j} → (ab : Σ A B) → ab == (fst ab , snd ab)
  upptΣ _ = refl

module Ex1-4 where

  -- open import lib.types.Sigma

  {-
  Assuming as given only the iterator for natural numbers
  iter : ∏ C → (C → C) → N → C
       C:U
  with the defining equations
  iter(C, c0, cs, succ(n)) :≡ cs(iter(C, c0, cs, n)),
  derive a function having the type of the recursor recN. Show that the defining
  equations of the recursor hold propositionally for this function, using the
  induction principle for N.
  -}

  iter : {C : Type0} →
    C → (C → C) → ℕ → C
  iter c0 cs 0 = c0
  iter c0 cs (S n) = cs (iter c0 cs n)

  -- used in the definition of recNiter below to keep a count of the applications of a function
  sucApply : {C : Type0} → (ℕ → C → C) → ℕ × C → ℕ × C
  sucApply {C} cs = cs' where
    cs' : ℕ × C → ℕ × C
    cs' (n , c) = S n , cs n c

  {- Induction principle (dependent eliminator) for ℕ from the book:

  indN : ∏(C:N→U)C(0) → ∏(n:N)C(n) → C(succ(n)) → ∏(n:N)C(n)
  indN(C, c0, cs, 0) :≡ c0,
  indN(C, c0, cs, succ(n)) :≡ cs(n, indN(C, c0, cs, n)).
  -}
  indN : ∀ {i} {C : ℕ → Type i} →
    C 0 → ((n : ℕ) → C n → C (S n)) → (n : ℕ) → C n
  indN c0 cs 0 = c0
  indN c0 cs (S n) = cs n (indN c0 cs n)

  -- digression / warmup - inductive proof that evens-are-even

  -- nth even
  even : ℕ → ℕ
  even n = iter 0 (λ n → S (S n)) n

  S= : {m n : ℕ} → m == n → (S m == S n)
  S= refl = refl

  _*2 : ℕ → ℕ
  O *2 = O
  (S n) *2 = S (S (n *2))

  evens-are-even : (n : ℕ) → Σ ℕ (λ m → even n == m *2)
  evens-are-even = indN (0 , refl) inductiveCase where
    inductiveCase : (n : ℕ) → Σ ℕ (λ m → even n == m *2) → Σ ℕ (λ m → even (S n) == m *2)
    inductiveCase n (m , p) = S m , p'' where
      p' = S= p
      p'' = S= p'

  {- derive a function having the type of the recursor recN
  recN : ∏(C:U)C→(N→C→C)→N→C
  recN(C, c0, cs, 0) :≡ c0,
  recN(C, c0, cs, Sc(n)) :≡ cs(n, recN(C, c0, cs, n)).
  -}
  recNiter : {C : Type0} →
    C → (ℕ → C → C) → ℕ → C
  recNiter c0 cs n = snd (iter (0 , c0) cs' n) where
           cs' = sucApply cs

  {- Show that the defining
  equations of the recursor hold propositionally for this function, using the
  induction principle for N
  -}
  recNiter= : {C : Type0} {c0 : C} {cs : ℕ → C → C } →
    (n : ℕ) →
    (recNiter c0 cs (S n)) == (cs n (recNiter c0 cs n))
  recNiter= {C} {c0} {cs} n = cs= n'= -- or, as spelled out below (using equational reasoning from HoTT-Agda)
    -- recNiter c0 cs (S n) =⟨ refl ⟩
    -- snd (iter' (S n)) =⟨ refl ⟩
    -- snd (cs' (iter' n)) =⟨ refl ⟩
    -- snd (cs' (n' , snd (iter' n))) =⟨ refl ⟩
    -- cs n' (snd (iter' n)) =⟨ cs= n'= ⟩
    -- cs n (snd (iter' n)) =⟨ refl ⟩
    -- cs n (recNiter c0 cs n) ∎
    where
      cs' = sucApply cs

      iter' : ℕ → ℕ × C
      iter' = iter (0 , c0) cs'

      n' = fst (iter' n)

      -- proof that the first (counter) projection of the iter version of recN at n is just n
      fstIter'= : (n : ℕ) → (fst (iter (0 , c0) cs' n) == n)
      fstIter'= = indN refl inductiveCase where
        inductiveCase : (n : ℕ) →
          fst (iter' n) == n →
          fst (iter' (S n)) == S n
        inductiveCase m p = S= p -- or, as spelled out below
          -- fst (iter (0 , c0) cs' (S m)) =⟨ refl ⟩
          -- fst (cs' (iter (0 , c0) cs' m)) =⟨ refl ⟩
          -- fst (cs' (iter (0 , c0) cs' m)) =⟨ refl ⟩
          -- -- fst (cs' (fst (iter (0 , c0) cs' m) , _)) =⟨ refl ⟩ -- Agda loses track of some hidden
          -- -- fst (S (fst (iter (0 , c0) cs' m)) , _) =⟨ refl ⟩ -- type data here, thus double-protective comments
          -- S (fst (iter (0 , c0) cs' m)) =⟨ S= p ⟩
          -- S m ∎

      n'= : n' == n
      n'= = fstIter'= n

      cs= : ∀ {n m} {c : C} → n == m → cs n c == cs m c
      cs= refl = refl

-- recursor for Bool (used in next two exercises)
module RecBool where
  recBool : ∀ {i} {A : Type i} → A → A → Bool → A
  recBool x y true = x
  recBool x y false = y

module Ex1-5 where
  open RecBool
  {-
  Exercise 1.5. Show that if we define A + B :≡ ∑(x:2) rec2(U, A, B, x), then we can give a definition
  of indA+B for which the definitional equalities stated in §1.7 hold.
  -}
  _+_ : ∀ {i} → Type i → Type i → Type _
  A + B = Σ Bool (λ isA → recBool A B isA)

  inl-+ : ∀ {i} {A B : Type i} → A → A + B
  inl-+ a = true , a

  inr-+ : ∀ {i} {A B : Type i} → B → A + B
  inr-+ b = false , b

  ind-+ : ∀ {i j} {A B : Type i} (C : A + B → Type j) →
    ((a : A) → C (inl-+ a)) → ((b : B) → C (inr-+ b)) →
    (x : A + B) → C x
  ind-+ C g1 g2 (true , a) = g1 a
  ind-+ C g1 g2 (false , b) = g2 b

module Ex1-6 {i} {A B : Type i} where
  open RecBool
  open import FunExt
  {-
  Exercise 1.6. Show that if we define A × B :≡ ∏(x:2) rec2(U, A, B, x), then we can give a defini- tion of indA×B for which the definitional equalities stated in §1.5 hold propositionally (i.e. using equality types). (This requires the function extensionality axiom, which is introduced in §2.9.)
  -}

  _x_ : ∀ {i} → (A : Type i) → (B : Type i) → Type _
  A x B = Π Bool (λ ab → recBool A B ab)

  _,,_ : A → B → A x B
  _,,_ a b true = a
  _,,_ a b false = b

  fst-x : A x B → A
  fst-x ab = ab true

  snd-x : A x B → B
  snd-x ab = ab false

  uppt-x : (ab : (A x B)) → (fst-x ab ,, snd-x ab) == ab
  uppt-x ab = is-equiv.g fe h where -- (fst-x ab ,, snd-x ab) x == ab x
    fe = fun-ext ((fst-x ab ,, snd-x ab)) ab
    h : (c : Bool) → (fst-x ab ,, snd-x ab) c == ab c
    h true = refl
    h false = refl

  ind-x : ∀ {j} (C : A x B → Type j) →
    ((a : A) → (b : B) → C (a ,, b)) →
    (ab : A x B) → C ab
  ind-x C g ab = transport C (uppt-x ab) (g a b) where
    a = fst-x ab
    b = snd-x ab

module Ex1-7 {i} {A B : Type i} where
  {-
  Exercise 1.7. Give an alternative derivation of ind′=A from ind=A which avoids the use of universes. (This is easiest using concepts from later chapters.)
  -}
