{-# OPTIONS --without-K #-}

module Ch2 where

  open import lib.Base

  {- Free path induction, or as close as I could get, written in Section 1.12.1 as

  ind=A : ∏ ∏(x:A)C(x,x,reflx) → ∏ ∏ C(x,y,p) (C:∏(x,y:A)(x=Ay)→U) (x,y:A) (p:x=Ay)
  ind=A (C, c, x, x, reflx) :≡ c(x)
  -}
  ind== : ∀ {i j} {A : Type i} (D : (x y : A) → x == y → Type j) (d : (x : A) → D x x idp)
    {x y : A} (p : x == y) → D x y p
  ind== D d {x} idp = d x -- slight concern: what are the rules for implicit {x} and {y}
                          -- converging on the single {x} parameter here?  I don't know Agda
                          -- well enough to answer this yet.  Depending upon what
                          -- they are, this rule may be a duplicate of one of the based
                          -- path induction rules below.

  {- Based path induction, or the J rule in HoTT-Agda lib -}
  ind=' : ∀ {i j} {A : Type i} {a : A} (D : (x : A) (p : a == x) → Type j) (d : D a idp)
    {x : A} (p : a == x) → D x p
  ind=' D d idp = d

  {- Right-based path induction, or J' in the HoTT-Agda lib -}
  ind'= : ∀ {i j} {A : Type i} {a : A} (D : (x : A) (p : x == a) → Type j) (d : D a idp)
    {x : A} (p : x == a) → D x p
  ind'= D d idp = d


{-
Lemma 2.1.2. For every type A and every x, y, z : A there is a function
 (x = y) → (y = z) → (x = z)
written p → q → p ∙ q, such that reflx ∙ reflx ≡ reflx for any x : A. 

We call p ∙ q the concatenation or composite of p and q.

Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.
-}

-- proof of 2.1.2 are inhabitants

  module Ex2-1 where

  open import lib.Base

  {- The versions of concat below WITHOUT the primes 's are proved using Agda's
  'internal J rule', whatever that might be.  In the HoTT-Agda lib, there is a
  comment that:

  "At the time I’m writing this (July 2013), the identity type is somehow broken in
  Agda dev, it behaves more or less as the Martin-Löf identity type instead of
  behaving like the Paulin-Mohring identity type."

  concat1' and concat3' are proved using ind== which is the closest I could get
  to free path induction (as in the book), but unfortunately this didn't work out
  for concat2' which had to use left-based path induction, ie ind=' (J in the
  HoTT-Agda libs)
  -}

  concat1 : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat1 idp q = q

  concat1' : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat1' {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → (p : x == y) → Type i
    D x y _ = y == z → x == z

    d : (x₁ : A) → D x₁ x₁ idp
    d _ = λ q → q

  concat2 : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat2 p idp = p
  
  -- uses based path induction, because I couldn't get free path induction to work
  concat2' : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat2' {i} {A} {x} {y} {_} p = ind=' D d where
    D : (z : A) → y == z → Type i
    D z _ = x == z

    d : D _ idp
    d = p

  concat3 : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat3 idp idp = idp

  concat3' : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat3' {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → (p : x == y) → Type i
    D x y _ = y == z → x == z

    d : (x₁ : A) → D x₁ x₁ idp
    d _ = ind== E e where
      E : (y z : A) (q : y == z) → Type i
      E y z _ = y == z

      e : (x : A) → E x x idp
      e _ = idp

  concat1=concat2 : ∀ {i} {A : Type i} {x y z : A} 
    (p : x == y) (q : y == z) → concat1 p q == concat2 p q
  concat1=concat2 idp idp = idp

  concat1'=concat2' : ∀ {i} {A : Type i} {x y z : A} 
    (p : x == y) (q : y == z) → concat1' p q == concat2' p q
  concat1'=concat2' {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) → concat1' p q == concat2' p q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y₁ z₁ : A) → y₁ == z₁ → Type i
      E _ _ q = concat1' idp q == concat2' idp q

      e : (x₁ : A) → E x₁ x₁ idp
      e _ = idp -- : concat1' idp idp == concat2' idp idp
                -- > (ind== D d) idp idp == (ind== D d) idp idp
                -- > (d1 x) idp = (d2 x) idp
                -- > idp == idp -- (this being the type of the inhabitant value idp of e x)

  concat2=concat3 : ∀ {i} {A : Type i} {x y z : A} 
    (p : x == y) (q : y == z) → concat2 p q == concat3 p q
  concat2=concat3 idp idp = idp

  concat2'=concat3' : ∀ {i} {A : Type i} {x y z : A} 
    (p : x == y) (q : y == z) → concat2' p q == concat3' p q
  concat2'=concat3' {i} {A} {x} {y} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) → concat2' p q == concat3' p q

    d : (x : A) → D x x idp
    d x = ind== E e where
      E : (y₁ z₁ : A) → y₁ == z₁ → Type i
      E _ _ q = concat2' idp q == concat3' idp q

      e : (x₁ : A) → E x₁ x₁ idp
      e _ = idp -- : concat2' idp idp == concat3' idp idp

  concat1=concat3 : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) → concat1 p q == concat3 p q
  concat1=concat3 idp idp = idp

  concat1'=concat3' : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) → concat1' p q == concat3' p q
  concat1'=concat3' {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D x y p = (q : y == z) → concat1' p q == concat3' p q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y z : A) → (q : y == z) → Type i
      E _ _ q = concat1' idp q == concat3' idp q

      e : (y : A) → E y y idp
      e _ = idp -- : concat1' idp idp == concat3' idp idp

  module Ex2-2 where

  {-
  Show that the three equalities of proofs constructed in the previous exercise form a
  commutative triangle. In other words, if the three definitions of concatenation are denoted
  by (p 􏰂1 q), (p 􏰂2 q), and (p 􏰂3 q), then the concatenated equality
  (p 􏰂1 q) = (p 􏰂2 q) = (p 􏰂3 q)
  is equal to the equality 
  (p 􏰂1 q) = (p 􏰂3 q).
  -}

  -- A choice of which 'concat' we use for the statement of the proof term; we use the book one
  concat = concat3

  concat-commutative-triangle : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) →
    concat (concat1=concat2 p q) (concat2=concat3 p q) == concat1=concat3 p q
  concat-commutative-triangle idp idp = idp

  -- likewise, the ind== version of the book concat operator
  concat' = concat3'

  concat-commutative-triangle' : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) →
    concat' (concat1'=concat2' p q) (concat2'=concat3' p q) == concat1'=concat3' p q
  concat-commutative-triangle' {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) → concat' (concat1'=concat2' p q) (concat2'=concat3' p q) == concat1'=concat3' p q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y z : A) → (q : y == z) → Type i
      E _ _ q = concat' (concat1'=concat2' idp q) (concat2'=concat3' idp q) == concat1'=concat3' idp q

      e : (y : A) → E y y idp
      e _ = idp -- : concat' (concat1'=concat2' idp idp) (concat2'=concat3' idp idp) == concat1'=concat3' idp idp
