{- OPTIONS --without-K -}

module Base where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

Type : (i : Level) → Set (lsuc i)
Type i = Set i

Type₀ = Type lzero
Type0 = Type lzero

Type₁ = Type (lsuc lzero)
Type1 = Type (lsuc lzero)

{- Naturals -}

data ℕ : Type₀ where
  O : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

infix 3 _==_

data _==_ {i} {A : Type i} (a : A) : A → Type i where
  refl : a == a

Path = _==_

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL  refl #-}

{- Free path induction, or as close as I could get, written in Section 1.12.1 as

ind=A : ∏ ∏(x:A)C(x,x,reflx) → ∏ ∏ C(x,y,p) (C:∏(x,y:A)(x=Ay)→U) (x,y:A) (p:x=Ay)
ind=A (C, c, x, x, reflx) :≡ c(x)
-}
ind== : ∀ {i j} {A : Type i} (D : (x y : A) → x == y → Type j) (d : (x : A) → D x x refl)
  {x y : A} (p : x == y) → D x y p
ind== D d {x} refl = d x -- slight concern: what rules govern the implicit {x} and {y}
                        -- converging on the single {x} parameter here?  I don't know Agda
                        -- well enough to answer this yet.  Depending upon what
                        -- they are, this rule may be a duplicate of one of the based
                        -- path induction rules below.

{- Based path induction, or the J rule in HoTT-Agda lib -}
ind=' : ∀ {i j} {A : Type i} {a : A} (D : (x : A) (p : a == x) → Type j) (d : D a refl)
  {x : A} (p : a == x) → D x p
ind=' D d refl = d

{- Right-based path induction, or J' in the HoTT-Agda lib -}
ind'= : ∀ {i j} {A : Type i} {a : A} (D : (x : A) (p : x == a) → Type j) (d : D a refl)
  {x : A} (p : x == a) → D x p
ind'= D d refl = d

ind==2 : ∀ {i j} {A : Type i} (D : {x y : A} → x == y → Type j) (d : {x : A} → D {x} {x} refl)
  {x y : A} (p : x == y) → D p
ind==2 D d refl = d -- slight concern: what rules govern the implicit {x} and {y}

-- {- Alternative based path induction as a specialized free path induction -}
-- ind='2 : ∀ {i j} {A : Type i} {a : A} (D : {x : A} (p : a == x) → Type j) (d : D refl)
--   {x : A} (p : a == x) → D p
-- ind='2 D d = ind==2 {!!} {!!}

-- Christine Paulin-Mohring’s version of the J rule is based path induction ind='
J : ∀ {i j} {A : Type i} {a : A} (D : {x : A} → a == x → Type j) → D refl →
  {x : A} (p : a == x) → D p
J D d refl = d


{- Unit type

The unit type is defined as record so that we also get the η-rule definitionally.
-}

record Unit : Type₀ where
  constructor unit

{- Dependent paths

The notion of dependent path is a very important notion.
If you have a dependent type [B] over [A], a path [p : x == y] in [A] and two
points [u : B x] and [v : B y], there is a type [u == v [ B ↓ p ]] of paths from
[u] to [v] lying over the path [p].
By definition, if [p] is a constant path, then [u == v [ B ↓ p ]] is just an
ordinary path in the fiber.
-}

PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
PathOver B refl u v = (u == v)

syntax PathOver B p u v =
  u == v [ B ↓ p ]

{- Ap, coe and transport

Given two fibrations over a type [A], a fiberwise map between the two fibrations
can be applied to any dependent path in the first fibration ([ap↓]).
As a special case, when [A] is [Unit], we find the familiar [ap] ([ap] is
defined in terms of [ap↓] because it shouldn’t change anything for the user
and this is helpful in some rare cases)
-}

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f refl = refl

ap↓ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (g : {a : A} → B a → C a) {x y : A} {p : x == y}
  {u : B x} {v : B y}
  → (u == v [ B ↓ p ] → g u == g v [ C ↓ p ])
ap↓ g {p = refl} p = ap g p

{-
[apd↓] is defined in lib.PathOver. Unlike [ap↓] and [ap], [apd] is not
definitionally a special case of [apd↓]
-}

apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f refl = refl

{-
An equality between types gives two maps back and forth
-}

coe : ∀ {i} {A B : Type i} (p : A == B) → A → B
coe refl x = x

coe! : ∀ {i} {A B : Type i} (p : A == B) → B → A
coe! refl x = x

{-
The operations of transport forward and backward are defined in terms of [ap]
and [coe], because this is more convenient in practice.
-}

transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B x → B y)
transport B p = coe (ap B p)

transport! : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B y → B x)
transport! B p = coe! (ap B p)

{- Equational reasoning

Equational reasoning is a way to write readable chains of equalities.
The idea is that you can write the following:

  t : a == e
  t = a =⟨ p ⟩
      b =⟨ q ⟩
      c =⟨ r ⟩
      d =⟨ s ⟩
      e ∎

where [p] is a path from [a] to [b], [q] is a path from [b] to [c], and so on.

You often have to apply some equality in some context, for instance [p] could be
[ap ctx thm] where [thm] is the interesting theorem used to prove that [a] is
equal to [b], and [ctx] is the context.
In such cases, you can use instead [thm |in-ctx ctx]. The advantage is that
[ctx] is usually boring whereas the first word of [thm] is the most interesting
part.

_=⟨_⟩ is not definitionally the same thing as concatenation of paths _∙_ because
we haven’t defined concatenation of paths yet, and also you probably shouldn’t
reason on paths constructed with equational reasoning.
If you do want to reason on paths constructed with equational reasoning, check
out lib.types.PathSeq instead.
-}

infix  2 _∎
infixr 2 _=⟨_⟩_

_=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x == y → y == z → x == z
_ =⟨ refl ⟩ refl = refl

_∎ : ∀ {i} {A : Type i} (x : A) → x == x
_ ∎ = refl

syntax ap f p = p |in-ctx f


{- Coproducts and case analysis -}

data Coprod {i j} (A : Type i) (B : Type j) : Type (i ⊔ j) where
  inl : A → Coprod A B
  inr : B → Coprod A B

{- Σ-types

Σ-types are defined as a record so that we have definitional η.
-}

infix 1 _,_

record Σ {i j} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

pair= : ∀ {i j} {A : Type i} {B : A → Type j}
  {a a' : A} (p : a == a') {b : B a} {b' : B a'}
  (q : b == b' [ B ↓ p ])
  → (a , b) == (a' , b')
pair= refl q = ap (_,_ _) q

pair×= : ∀ {i j} {A : Type i} {B : Type j}
  {a a' : A} (p : a == a') {b b' : B} (q : b == b')
  → (a , b) == (a' , b')
pair×= refl q = pair= refl q


{- Empty type

We define the eliminator of the empty type using an absurd pattern. Given that
absurd patterns are not consistent with HIT, we will not use empty patterns
anymore after that.
-}

data Empty : Type₀ where

Empty-elim : ∀ {i} {A : Empty → Type i} → ((x : Empty) → A x)
Empty-elim ()


{- Negation and disequality -}

¬ : ∀ {i} (A : Type i) → Type i
¬ A = A → Empty

_≠_ : ∀ {i} {A : Type i} → (A → A → Type i)
x ≠ y = ¬ (x == y)

-- Cartesian product
_×_ : ∀ {i j} (A : Type i) (B : Type j) → Type _
A × B = Σ A (λ _ → B)

⊥ = Empty

{- Π-types

Shorter notation for Π-types.
-}

Π : ∀ {i j} (A : Type i) (P : A → Type j) → Type _
Π A P = (x : A) → P x

{- Bool type -}

data Bool : Type₀ where
  true : Bool
  false : Bool


{- Equivalences -}

_~_ : ∀ {i} {A : Type i} {B : Type i} -> (f : A -> B) -> (g : A -> B) -> Type i
_~_ {_} {A} {_} f g = Π A λ x -> (f x) == (g x)

id : ∀ {i} {A : Type i} -> (A -> A)
id a = a

_∘_ : ∀ {i} {A : Type i} {B : Type i} {C : Type i} -> (g : B -> C) -> (f : A -> B) -> (A -> C)
_∘_ g f x = g (f x)

module _ {i} {A B : Type i} where

  -- We take the canonical type for equivalences to be half adjoint equivalences
  record is-equiv (f : A → B) : Type i where
    constructor equiv
    field
      g : B → A
      η : (g ∘ f) ~ id
      ε : (f ∘ g) ~ id
      τ : (a : A) → ap f (η a) == ε (f a)

{- Equivalences without record types -}


{- Quasi inverse -}
q-inv : ∀ {i} {A : Type i} {B : Type i} -> (f : A -> B) -> Type i
q-inv {_} {A} {B} f = Σ (B -> A) λ g -> (((f ∘ g) ~ id) × ((g ∘ f) ~ id))

{- Equivalence -}
is-equiv' : ∀ {i} {A : Type i} {B : Type i} -> (f : A -> B) -> Type i
is-equiv' {_} {A} {B} f = (Σ (B -> A) λ g -> ((f ∘ g) ~ id)) × (Σ (B -> A) λ h -> ((h ∘ f) ~ id))

{- Every map with a quasi inverse is an equivalence -}
q-inv-to-equiv' : ∀ {i} {A : Type i} {B : Type i} -> (f : A -> B) -> (q-inv f) -> (is-equiv' f)
q-inv-to-equiv' f q = (( g , h1 ) , (g , h2)) where
  g = fst q
  h1 = fst (snd q)
  h2 = snd (snd q)
