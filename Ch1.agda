{-# OPTIONS --without-K #-}

module Ch1 where

  open import lib.Base

  -- warmup
  module Eq-1-11-2 where
  
    -- import lib.types.Coproduct
    open import lib.types.Empty
    open import lib.types.Sigma
    
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
    o-assoc _ _ _ = idp -- "it's de proof"
  
  module Ex1-2 where
    
    open import lib.types.Sigma

    -- Derive the recursion principle for products recA×B using only the projections, and
    -- verify that the definitional equalities are valid. Do the same for Σ-types.
    
    recAxB : {A B C : Type0} →
      (A → B → C) → A × B → C
    recAxB f ab = f (fst ab) (snd ab)
    
    recAxB= : ∀ {A B C} 
      {f : A → B → C}
      {a : A} {b : B} →
      recAxB f (a , b) == f a b
    recAxB= = idp
    
    recA+B : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} →
      (A → C) → (B → C) → (Coprod A B → C)
    recA+B f g (inl x) = f x
    recA+B f g (inr x) = g x
    
    recA+B= : {A B C : Type0}
      {f : A → C} {g : B → C}
      {a : A} {b : B} →
      (recA+B f g (inl a) == f a) × (recA+B f g (inr b) == g b)
    recA+B= = idp , idp
    
    recΣ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k} →
      ((a : A) → B a → C) →
      Σ A B → C
    recΣ f ab = f (fst ab) (snd ab)
    
    recΣ= : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k}
      {f : (a : A) → B a → C}
      {a : A} {ba : B a} →
      recΣ f (a , ba) == f a ba
    recΣ= = idp

  module Ex1-3 where
    
    open import lib.types.Sigma

    {- Derive the induction principle for products indA×B, using only the projections
    and the propositional uniqueness principle uppt. Verify that the definitional 
    equalities are valid. Gen- eralize uppt to Σ-types, and do the same for Σ-types. 
    -}
    
    -- book definition of uppt
    upptAxB : ∀ {i j} {A : Type i} {B : Type j} →
      (x : (A × B)) → (fst x , snd x) == x
    upptAxB = λ _ → idp
    
    -- definition of induction principle using only the projections
    indAxB : ∀ {i j k} {A : Type i} {B : Type j} → 
      (C :  (A × B) → Type k) →
      Π A (λ x → Π B (λ y → C (x , y))) → Π (A × B) C
    indAxB _ g ab = g (fst ab) (snd ab)
    
    -- book definition of induction principle using pattern matching
    indAxB2 : ∀ {i j k} {A : Type i} {B : Type j} → 
      (C :  (A × B) → Type k) →
      Π A (λ x → Π B (λ y → C (x , y))) → Π (A × B) C
    indAxB2 _ g (a , b) = g a b
    
    -- another definition of uniqueness principle upptAxBind (using induction principle)
    upptAxBind : ∀ {i j} {A : Type i} {B : Type j} →
      (x : (A × B)) → (fst x , snd x) == x
    upptAxBind = indAxB (λ z → z == z) (λ x x₁ → idp)
    
    -- validate definition for uppt
    upptAxB= : ∀ {i j} {A : Type i} {B : Type j} {x : (A × B)} →
      (upptAxB x) == (upptAxBind x)
    upptAxB= = idp
    
    -- uppt for Σ types
    upptΣ : ∀ {i j} {A : Type i} {B : A → Type j} →
      (ab : Σ A B) → (fst ab , snd ab) == ab
    upptΣ _ = idp
  
  module Ex1-4 where
  
    open import lib.types.Sigma

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
  
    data ℕ : Type₀ where
      zero : ℕ
      suc : (n : ℕ) → ℕ
    
    {-# BUILTIN NATURAL ℕ #-}
    {-# BUILTIN ZERO zero #-}
    {-# BUILTIN SUC suc #-}
    
    iter : {C : Type0} →
      C → (C → C) → ℕ → C
    iter c0 cs 0 = c0
    iter c0 cs (suc n) = cs (iter c0 cs n)

    -- used in the definition of recNiter below to keep a count of the applications of a function
    sucApply : {C : Type0} → (ℕ → C → C) → ℕ × C → ℕ × C
    sucApply {C} cs = cs' where
      cs' : ℕ × C → ℕ × C
      cs' (n , c) = suc n , cs n c
    
    {- Induction principle (dependent eliminator) for ℕ from the book:
    
    indN : ∏(C:N→U)C(0) → ∏(n:N)C(n) → C(succ(n)) → ∏(n:N)C(n)
    indN(C, c0, cs, 0) :≡ c0,
    indN(C, c0, cs, succ(n)) :≡ cs(n, indN(C, c0, cs, n)).
    -}
    indN : ∀ {i} {C : ℕ → Type i} → 
      C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
    indN c0 cs 0 = c0
    indN c0 cs (suc n) = cs n (indN c0 cs n)
    
    -- digression / warmup - inductive proof that evens-are-even
    
    -- nth even
    even : ℕ → ℕ
    even n = iter 0 (λ n → suc (suc n)) n
    
    suc= : {m n : ℕ} → m == n → (suc m == suc n)
    suc= idp = idp
    
    _*2 : ℕ → ℕ
    zero *2 = zero
    (suc n) *2 = suc (suc (n *2))
    
    evens-are-even : (n : ℕ) → Σ ℕ (λ m → even n == m *2)
    evens-are-even = indN (0 , idp) inductiveCase where
      inductiveCase : (n : ℕ) → Σ ℕ (λ m → even n == m *2) → Σ ℕ (λ m → even (suc n) == m *2)
      inductiveCase n (m , p) = suc m , p'' where
        p' = suc= p
        p'' = suc= p'
    
    {- derive a function having the type of the recursor recN
    recN : ∏(C:U)C→(N→C→C)→N→C
    recN(C, c0, cs, 0) :≡ c0,
    recN(C, c0, cs, succ(n)) :≡ cs(n, recN(C, c0, cs, n)).
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
      (recNiter c0 cs (suc n)) == (cs n (recNiter c0 cs n))
    recNiter= {C} {c0} {cs} n = cs= n'= -- or, as spelled out below (using equational reasoning from HoTT-Agda)
      -- recNiter c0 cs (suc n) =⟨ idp ⟩
      -- snd (iter' (suc n)) =⟨ idp ⟩
      -- snd (cs' (iter' n)) =⟨ idp ⟩
      -- snd (cs' (n' , snd (iter' n))) =⟨ idp ⟩
      -- cs n' (snd (iter' n)) =⟨ cs= n'= ⟩
      -- cs n (snd (iter' n)) =⟨ idp ⟩
      -- cs n (recNiter c0 cs n) ∎
      where
        cs' = sucApply cs
    
        iter' : ℕ → ℕ × C
        iter' = iter (0 , c0) cs'
    
        n' = fst (iter' n)
    
        -- proof that the first (counter) projection of the iter version of recN at n is just n
        fstIter'= : (n : ℕ) → (fst (iter (0 , c0) cs' n) == n)
        fstIter'= = indN idp inductiveCase where
          inductiveCase : (n : ℕ) → 
            fst (iter' n) == n →
            fst (iter' (suc n)) == suc n
          inductiveCase m p = suc= p -- or, as spelled out below
            -- fst (iter (0 , c0) cs' (suc m)) =⟨ idp ⟩
            -- fst (cs' (iter (0 , c0) cs' m)) =⟨ idp ⟩
            -- fst (cs' (iter (0 , c0) cs' m)) =⟨ idp ⟩
            -- -- fst (cs' (fst (iter (0 , c0) cs' m) , _)) =⟨ idp ⟩ -- Agda loses track of some hidden
            -- -- fst (suc (fst (iter (0 , c0) cs' m)) , _) =⟨ idp ⟩ -- type data here, thus double-protective comments
            -- suc (fst (iter (0 , c0) cs' m)) =⟨ suc= p ⟩
            -- suc m ∎
    
        n'= : n' == n
        n'= = fstIter'= n
    
        cs= : ∀ {n m} {c : C} → n == m → cs n c == cs m c
        cs= idp = idp
