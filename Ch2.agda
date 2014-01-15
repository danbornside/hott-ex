{-# OPTIONS --without-K #-}

module Ch2 where

-- open import lib.Base
open import Base
                      
module Ex2-1 where
  {-
  Lemma 2.1.2. For every type A and every x, y, z : A there is a function
  (x = y) → (y = z) → (x = z)
  written p → q → p ∙ q, such that reflx ∙ reflx ≡ reflx for any x : A. 
                                                                   
  We call p ∙ q the concatenation or composite of p and q.
  -}
   
  {-                                                      
  Exercise 2.1 Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.
  -}

  -- (proof(s) of 2.1.2 are the inhabitants of the type corresponding to the
  -- statement of the lemma)

  {- The versions of concat below WITHOUT the primes 's are proved using Agda's
  'internal J rule', whatever that might be.  In the HoTT-Agda lib, there is a
  comment that:

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

  -- here is the free path induction version which didn't work.. amazingly it typechecks (with a warning)
  concat2'' : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat2'' {i} {A} {x} {y} {_} = λ p q → ind== D d q where
    D : (y z : A) → (q : y == z) → Type i
    D _ z _ = x == z
                   
    d : (y : A) → D y y idp
    d y = _  -- <<<<< I want to use p here, but can't since the free endpoint y in d needs to be 
             -- restricted to the y' that p : x == y' connects to (and I don't know how to talk
             -- Agda into this).  In fact, on reflection, it is probably to be expected that
             -- since p is alreay given, we can only used left-based path induction from the 
             -- point y' that p has already connected to, as-in the definition of concat2' above

  concat2''' : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat2''' {i} {A} {x} {y} {z} p = ind==2 D d where
    D : {y z : A} → (q : y == z) → Type i
    D {_} {z} _ = x == z
                   
    d : {y' : A} → D {y'} {y'} idp
    d {yy} = {!!}  -- <<<<< I want to use p here, but can't since the free endpoint y in d needs to be 

  concatTwo : ∀ {i} {A : Type i} {x y z : A} → (y == z) → (x == y) → (x == z)
  concatTwo {i} {A} {x} {_} {_} = ind== D d where
    D : (y z : A) → (q : y == z) → Type i
    D y z _ = x == y → x == z

    d : (y : A) → D y y idp
    d _ = λ q → q

  twist : ∀ {i} {A : Type i} {x y z : A} → ((y == z) → (x == y) →
          (x == z)) → ((x == y) → (y == z) → (x == z))
  twist conc = λ p → λ q → conc q p

  concat2'''' : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
  concat2'''' = twist concatTwo

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
      e _ = idp -- : concat1' idp idp == concat2' idp idp   ⇓'p'
                -- > (ind== D1 d1) idp idp == (ind== D2 d2) idp idp 
                -- > (d1 q) idp == (d2 x) idp
                -- > (λ q → q) idp == 'p' (aka idp)
                -- > idp == idp -- (this being the type of the inhabitant value idp of e x)

  concat1'=concat2'''' : ∀ {i} {A : Type i} {x y z : A} 
    (p : x == y) (q : y == z) → concat1' p q == concat2'''' p q
  concat1'=concat2'''' {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) → concat1' p q == concat2'''' p q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y₁ z₁ : A) → y₁ == z₁ → Type i
      E _ _ q = concat1' idp q == concat2'''' idp q

      e : (x₁ : A) → E x₁ x₁ idp
      e _ = idp -- : concat1' idp idp == concat2' idp idp   ⇓'p'
                -- > (ind== D1 d1) idp idp == (ind== D2 d2) idp idp 
                -- > (d1 q) idp == (d2 x) idp
                -- > (λ q → q) idp == 'p' (aka idp)
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
             
  open Ex2-1
  
  {-
  Show that the three equalities of proofs constructed in the previous exercise form a
  commutative triangle. In other words, if the three definitions of concatenation are denoted
  by (p 􏰂1 q), (p 􏰂2 q), and (p 􏰂3 q), then the concatenated equality
  (p 􏰂1 q) = (p 􏰂2 q) = (p 􏰂3 q)
  is equal to the equality 
  (p 􏰂1 q) = (p 􏰂3 q).
  -}

  -- Choice of which 'concat' we use for the statement of the proof type; we use the book one
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
    D _ y p = (q : y == z) → 
      concat' (concat1'=concat2' p q) (concat2'=concat3' p q) == concat1'=concat3' p q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y z : A) → (q : y == z) → Type i
      E _ _ q = 
        concat' (concat1'=concat2' idp q) (concat2'=concat3' idp q) == concat1'=concat3' idp q

      e : (y : A) → E y y idp
      e _ = idp -- : concat' (concat1'=concat2' idp idp) (concat2'=concat3' idp idp) == concat1'=concat3' idp idp
                                                                                                              
module Ex2-3 where
             
  -- use another of the based path inductions
                                   
module Ex2-4 where
             
{- Define, by induction on n, a general notion of n-dimensional path in a type A,
simultaneously with the type of boundaries for such paths. -}
