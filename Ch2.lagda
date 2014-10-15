\documentclass{article}

% The following packages are needed because unicode
% is translated (using the next set of packages) to
% latex commands. You may need more packages if you
% use more unicode characters:

\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{textgreek}

% This handles the translation of unicode to latex:
%\usepackage[LGR, T1]{fontenc}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

% Some characters that are not automatically defined
% (you figure out by the latex compilation errors you get),
% and you need to define:

\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{9632}{\ensuremath{\ct}}
%\usepackage{newunicodechar}
%\newunicodechar{λ}{\ensuremath{\lambda}}

% Add more as you need them (shouldn’t happen often).

% Using “\newenvironment” to redefine verbatim to
% be called “code” doesn’t always work properly.
% You can more reliably use:

\usepackage{fancyvrb}

\DefineVerbatimEnvironment
   {code}{Verbatim}
   {} % Add fancy options here if you like.
\usepackage{amsthm}
\newtheorem*{lemma}{Lemma}
\newtheorem*{agda}{Agda Note}

\usepackage[all]{xy}
\usepackage{enumitem}
\usepackage{amsmath}
\usepackage{xspace}
\include{macros}

\begin{document}

%\newcommand{\refl}[1]{\ensuremath{\mbox{refl}_{#1}}}

\title{HoTT Chapter 2 Exercises}
\maketitle

\begin{code}
{-# OPTIONS --without-K #-}

module Ch2 where

open import Base
open import Ch1
\end{code}

\section{}

\begin{lemma}[2.1.2]
  For every type $A$ and every $x, y, z : A$ there is a function
  $(x = y) → (y = z) → (x = z)$
  written $p → q → p \ct q$, such that $\refl{x} \ct \refl{x} ≡ \refl{x}$ for any $x : A$.

  We call $p \ct q$ the concatenation or composite of $p$ and $q$.
\end{lemma}

  Exercise 2.1 Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.

\begin{proof}

(this justifies denoting ``the'' concatenation function as $ \ct $)

First, we need a type to inhabit. The type of any concatenation operator is

\[ \prod_{x,y,z : A} \prod_{p: x = y} \prod_{q: y = z} (x = z) \]



Thus far, the only tool we have to inhabit such a type is path induction. So, we first write down a family

\[ D_1(x,y,p) : \prod_{z:A} (y = z) → (x = z) \]

That is, given $x,y: A$ and a path from $x$ to $y$, we want a function that takes paths from $y$ to $z$ to paths from $x$ to $z$.

Path induction dictates that we now need a

\[ d_1 : \prod_{x:A} D(x,x, \refl{x}) \]

hence

\[ d_1(x) : \prod_{z:A} (x = z) → (x = z) \]

So, given a path from $x$ to $z$, we want a path from $x$ to $z$. We'll take the easy way out on this one!

\begin{code}
_■₁_ : ∀ {i} {A : Type i} {x y z : A} → (x == y) → (y == z) → (x == z)
_■₁_ {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → (p : x == y) → Type i
    D x y _ = y == z → x == z

    d : (x : A) → D x x refl
    d _ = λ q → q
\end{code}

For another construction, we do path induction in ``the other direction''.

That is, we will define

\[ D_2 : \prod_{y,z: A} \prod_{q: y = z} (x = y) → (x = z) \]

In other words, given $y$ and $z$ and a path from $y$ to $z$, we want a function that
takes paths from $x$ to $y$ to paths from $x$ to $z$.

Just like the previous proof, we need a

\[ d_2(y) : (y = z) → (y = z) \]

This is a bit trickier in Agda, because we really want to define a curried function

\[ (\ct_{2} \mbox{ } q) \mbox{ } p = p \ct q \]

However, we also want the type to be exactly the same as the types of the other constructions. Hence, we will use a twist map.

\begin{code}
_■₂_ : ∀ {i} {A : Type i} {x y z : A} → (x == y) → (y == z) → (x == z)
_■₂_ = twist concat2 where
    concat2 : ∀ {i} {A : Type i} {x y z : A} → (y == z) → (x == y) → (x == z)
    concat2 {i} {A} {x} {_} {_} = ind== D d where
      D : (y z : A) → (q : y == z) → Type i
      D y z _ = x == y → x == z

      d : (y : A) → D y y refl
      d _ = λ q → q
    twist : ∀ {i} {A : Type i} {x y z : A} → ((y == z) → (x == y) →
        (x == z)) → ((x == y) → (y == z) → (x == z))
    twist f = λ p → λ q → f q p

\end{code}

Note that these two constructions use path induction to reduce one side or the other to the ``identity'' path (in the first case $\refl{x}$ and in the second case $\refl{y}$). We can also do double induction to reduce both $p$ and $q$ to the $\refl{x}$ and $\refl{y}$.

We begin with the same type family as the first proof:

\[D_{1} : \prod_{x,y :A} \prod_{p:x = y} (y = z) → (x = z) \]

but we now wish to find a different inhabitant

\[d_{1}' (x) : (x = z) → (x = z) \]

We will use path induction to construct $d_{1}'$. We introduce a family:

\[ E : \prod_{x,z:A} \prod_{q: x = z} (x = z) \]

we now need

\[ e(x) : (x = x) \]

which is gotten quite easily:

\[ e(x) = \refl{x} \]

\begin{code}

_■₃_ : ∀ {i} {A : Type i} {x y z : A} → x == y → y == z → x == z
_■₃_ {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → (p : x == y) → Type i
    D x y _ = y == z → x == z

    d : (x₁ : A) → D x₁ x₁ refl
    d _ = ind== E e where
      E : (x z : A) (q : x == z) → Type i
      E x z _ = x == z

      e : (x : A) → E x x refl
      e _ = refl

\end{code}

We now want to show that these constructions are pairwise equal. By this,
we mean ``propositional equality'' - hence we must find paths between
each pair of constructions.

In each case, we perform a double induction on paths, first reducing
$p$ to $\refl{}$, and then reducing $q$ to $\refl{}$.

\begin{code}

■₁=■₂ : ∀ {i} {A : Type i} {x y z : A}
    (p : x == y) (q : y == z) → p ■₁ q == p ■₂ q
■₁=■₂ {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) →  p ■₁ q == p ■₂ q

    d : (x : A) → D x x refl
    d _ = ind== E e where
      E : (y₁ z₁ : A) → y₁ == z₁ → Type i
      E _ _ q = refl ■₁ q == refl ■₂ q

      e : (x₁ : A) → E x₁ x₁ refl
      e _ = refl

■₂=■₃ : ∀ {i} {A : Type i} {x y z : A}
    (p : x == y) (q : y == z) →  p ■₂ q == p ■₃ q
■₂=■₃ {i} {A} {x} {y} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) → p ■₂ q == p ■₃ q

    d : (x : A) → D x x refl
    d x = ind== E e where
      E : (y₁ z₁ : A) → y₁ == z₁ → Type i
      E _ _ q = refl ■₂ q == refl ■₃ q

      e : (x₁ : A) → E x₁ x₁ refl
      e _ = refl -- : concat2' refl refl == concat3' refl refl


■₁=■₃ : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) → p ■₁ q == p ■₃ q
■₁=■₃ {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D x y p = (q : y == z) →  p ■₁ q == p ■₃ q

    d : (x : A) → D x x refl
    d _ = ind== E e where
      E : (y z : A) → (q : y == z) → Type i
      E _ _ q =  refl ■₁ q == refl ■₃ q

      e : (y : A) → E y y refl
      e _ = refl -- : concat1' refl refl == concat3' refl refl
\end{code}
\end{proof}

\section{}

\begin{lemma}[2.2.1]

  The three equalities of proofs constructed in the previous exercise form a
  commutative triangle. In other words, if the three definitions of concatenation are denoted
  by $(p \ct_1 q)$, $(p \ct_2 q)$, and $(p \ct_3 q)$, then the concatenated equality

  \[ (p \ct_1 q) = (p \ct_2 q) = (p \ct_3 q) \]

  is equal to the equality

  \[ (p \ct_1 q) = (p \ct_3 q) \]

\end{lemma}

\begin{proof}

Despite the fact that we're working with the somewhat myserious type
of ``equalities of equalities'', this remains a statement about the
propositional equality of two paths. The only tool we have for
establishing such an equality is path induction.

First, we fix the definition of concatenation:

\begin{code}
_■_ = _■₁_

\end{code}

We must now show that, for all paths $p$, $q$, the proof that $p \ct_1 q$ is equal to
$p \ct_2 q$ followed by the proof that $p \ct_2 q$ is equal to $p \ct_3 q$ is equal to
the proof that $p \ct_1 q$ is equal to $p \ct_3 q$.

This is exactly expressed in the following type signature:


Since the theorem is quantified over two paths, we shall do double path induction.
So, it really just boils down to the theorem being true when both p and q
are the identity.

\begin{code}
concat-commutative-triangle : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) →
    (■₁=■₂ p q) ■ (■₂=■₃ p q) == ■₁=■₃ p q

concat-commutative-triangle {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) →
      (■₁=■₂ p q) ■ (■₂=■₃ p q) == ■₁=■₃ p q

    d : (x : A) → D x x refl
    d _ = ind== E e where
      E : (y z : A) → (q : y == z) → Type i
      E _ _ q =
        (■₁=■₂ refl q) ■ (■₂=■₃ refl q) == ■₁=■₃ refl q

      e : (y : A) → E y y refl
      e _ = refl

\end{code}
\end{proof}

At this point, it might be helpful to review the definitions of the different
concatenation functions. In particular, $\refl \ct \refl{} ≡ \refl{}$ where $\ct$
is any of $\ct_1$, $\ct_2$, or $\ct_3$.


\section{}

\section{}


Define, by induction on n, a general notion of n-dimensional path in a type A,
simultaneously with the type of boundaries for such paths.

We'll define $n$-paths recursively in terms of $n - 1$ paths by
recursion on $\mathbb{N}$. There are two cases. Given
a type $A$:

A $0$-path is an inhabitant of $A$.

A $n$-path, for $n > 0$, is an inhabitant of $p = q$ where $p$ and $q$ are
$(n - 1)$-paths.

I'm going to take two steps and then settle it once and for all!

\begin{code}
1paths : ∀ {i} (A : Type i) -> Type i
1paths A = Σ A (λ a -> Σ A (λ b -> (a == b)))

src : ∀ {i} {A : Type i} (p : (1paths A)) -> A
src p = fst p

dst : ∀ {i} {A : Type i} (p : (1paths A)) -> A
dst p = fst (snd p)

map : ∀ {i} {A : Type i} (p : (1paths A)) -> (src p) == (dst p)
map p = snd (snd p)

2paths : ∀ {i} (A : Type i) -> Type i
2paths A = Σ (1paths A) λ p -> Σ (1paths A) λ q →
  Σ ((src p) == (src q)) λ x → Σ ((dst p) == (dst q)) λ y →
    x ■ (map q) == (map p) ■ y

inverse : ∀ {i} {A : Type i} {a : A} {b : A} -> a == b -> b == a
inverse {i} {A} = ind== D d where
    D : (a b : A) (p : a == b) → Type i
    D a b _ = b == a

    d : (x : A) → D x x refl
    d _ = refl

2pathBoundary : ∀ {i} {A : Type i} -> 2paths A -> 1paths A
2pathBoundary (p , (q , (x , (y , α )))) = (src p , (src p ,
          ((x ■ (map q)) ■ (inverse y)) ■ (inverse (map p))))

\end{code}

3paths : ∀ {i} (A : Type i) -> Type i
3paths A = Σ (2paths A) λ p -> Σ (2paths A) λ q →
  Σ ((fst p) == (fst q)) λ x → Σ ((fst (snd p)) == (fst (snd q))) λ y →
    ( x ■ (snd (snd q))) == ((snd (snd p)) ■ y)

npaths : ∀ {i} (A : Type i) -> ℕ -> Type i
npaths {i} A 0 = 1paths A
npaths {i} A (S n) = Σ (npaths A n) λ p -> Σ (npaths A n) λ q →
  Σ ((fst p) == (fst q)) λ x → Σ ((fst (snd p)) == (fst (snd q))) λ y →
    ( x ■ (snd (snd q))) == ((snd (snd p)) ■ y)


This is not required by the exercise, but let's define the $n$-dimensional
identity by induction on $\mathbb{N}$. In topology, this would be the constant
map from the $n$-cube to a point.

%\begin{code}
refln : ∀ {i} (A : Type i) (a : A) -> (n : ℕ) -> npaths A n
-- TODO: Fix module stuff so I can write "indN" instead of "Ex1-4.indN"
refln A a = Ex1-4.indN (a , (a , refl)) E where
  E = λ n → λ q → q , (q , refl)

%\end{code}

Okay, now we have to define a boundary map on npaths. The boundary of an
n-path should be a pair of $(n-1)$-paths:

%\begin{code}
boundary : ∀ {i} {A : Type i} {n : ℕ} ->
  (npaths A (S n)) -> (npaths A n) × (npaths A n)
boundary {i} {A} {n} (p , (q , α)) = (p , q)
%\end{code}


%\begin{code}

boundaryHasEqualStart : ∀ {i} {A : Type i} {n : ℕ} ->
   (p : (npaths A (S n))) -> (fst (fst (boundary {i} {A} {n} p))) == (fst (snd (boundary {i} {A} {n} p)))
boundaryHasEqualStart {i} {A} {0} α = {!!} where
  p' : npaths A (S 0)
  p' = (fst (boundary {i} {A} {(S 0)} α ))
  p1 : npaths A 0
  p1 = fst p'
  p2 : npaths A 0
  p2 = fst (snd p')
  p : p2 == p1
  p = snd (snd p')
  q' : npaths A (S 0)
  q' = (snd (boundary {i} {A} {(S 0)} α))
  q1 : (npaths A 0)
  q1 = fst q'
  q2 : (npaths A 0)
  q2 = fst (snd q')
  q : q2 == q1
  q = snd (snd q')


boundaryHasEqualStart {i} {A} {(S n)} p = {!!} where
  q1 :  (npaths A (S (S n)))
  q1 = (fst (boundary {i} {A} {(S (S n))} p))
  q11 : (npaths A (S n))
  q11 = fst q1
  q12 : (npaths A (S n))
  q12 = fst (snd q1)
  α : q12 == q11
  α = snd (snd q1)
  q2 : (npaths A (S (S n)))
  q2 = (snd (boundary {i} {A} {(S (S n))} p))
  q21 : (npaths A (S n))
  q21 = fst q2
  q22 : (npaths A (S n))
  q22 = fst (snd q2)
  β : q22 == q21
  β = snd (snd q2)
--  γ : q12 == q22
--  γ = boundaryHasEqualStart

contBoundary : ∀ {i} {A : Type i} (n : ℕ) ->
  (npaths A (S (S n))) -> (npaths A (S n))
contBoundary n ( (q1 , (q2 , p1)) , ( (q1' , (q2' , p2)) , α )) = q1 , (q2' , {!!})

%\end{code}

\end{document}
