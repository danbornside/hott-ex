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

Let's try to do it one stage at a time:

\begin{itemize}
\item a 0-path is a point in $A$.
\item a 1-path is a path between 0-paths.
\end{itemize}

\begin{code}

0-path : ∀ {i} (A : Type i) -> Type i
0-path A = A

1-path : ∀ {i} (A : Type i) -> Type i
1-path A = Σ (0-path A) (λ a -> Σ (0-path A) (λ b -> (a == b)))

-- the boundary of a 1-path is a pair of 0-paths
δ₁ : ∀ {i} {A : Type i} -> (p : 1-path A) -> (0-path A) × (0-path A)
δ₁ (a , (b , p)) = (a , b)

\end{code}

The boundary of a 0-path is somewhat mysterious, so we shall leave it
undefined.

We now would like to define a 2-path as a path between 1-paths. However,
two arbitrary 1-paths look like this:

\[
\xymatrix{
a \ar[r]^-{p} & b \\
a' \ar[r]^-{q} & b' }
\]

That is, $p$ and $q$ are paths between different points. Hence, a path
between $p$ and $q$ doesn't make sense. That is, it's not well typed.

However, suppose we have paths $x,y$ as follows:

\[
\xymatrix{
a \ar[r]^-{p} \ar[d]^-{x} & b \ar[d]^-{y} \\
a' \ar[r]^-{q} & b' }
\]

It would certainly make sense to ask for a path of type $ p \ct y = x \ct q $.

So, it seems that to define 2-paths, we need pairs of 1-paths together with
vertical paths like $x$ and $y$ above. So we'll define it as a $\Sigma$-type:

\[ \Sigma_{p,q : \mbox{1-paths}} \Sigma_{x : \mbox{src p } = \mbox{ src q}}
   \Sigma_{ \mbox{dst p } = \mbox{ dst q}} p \ct y = x \ct q \]

We will write down some helper functions and then formalize this:

\begin{code}
-- Some convenience functions!
src : ∀ {i} {A : Type i} {a : A} {b : A} -> a == b -> A
src {_} {_} {a} {_} p = a

dst : ∀ {i} {A : Type i} {a : A} {b : A} -> a == b -> A
dst {_} {_} {_} {b} p = b

map : ∀ {i} {A : Type i} (p : (1-path A)) -> (fst p) == (fst (snd p))
map p = snd (snd p)

2-path : ∀ {i} (A : Type i) -> Type i
2-path A = Σ (1-path A) λ p -> Σ (1-path A) λ q →
  Σ ((src (map p)) == (src (map q))) λ x → Σ ((dst (map p)) == (dst (map q))) λ y →
    x ■ (map q) == (map p) ■ y

-- The boundary of a 2 path as a pair of 1 paths
δ₂ : ∀ {i} {A : Type i} -> 2-path A -> (1-path A) × (1-path A)
δ₂ {i} {A} (p , (q , (x , (y , α)))) = p , q
\end{code}

A boundary of a 2-path can be thought of as a loop. We can formalize this:

\begin{code}
-- Definition of inverses. This should be put somewhere else.
inverse : ∀ {i} {A : Type i} {a : A} {b : A} -> a == b -> b == a
inverse {i} {A} = ind== D d where
  D : (a b : A) (p : a == b) → Type i
  D a b _ = b == a
  d : (x : A) → D x x refl
  d _ = refl

-- Just to be cute - the boundary of a 2 path as a loop
δ₂-loop : ∀ {i} {A : Type i} -> 2-path A -> 1-path A
δ₂-loop (p , (q , (x , (y , α)))) =
  (src (map p) , (src (map p) ,
    ((x ■ (map q)) ■ (inverse y)) ■ (inverse (map p))))
\end{code}

If one tries to continue in this manner, the $\Sigma$-types will become
rather large! So it would be nice to appeal to some kind of recursion
at this point.

Luckily, it turns out that equality of inhabitants of $\Sigma$-types contain
all the lower dimensional equalities to make this work!

\begin{code}

n-path : ∀ {i} {A : Type i} -> ℕ -> Type i
n-path {i} {A} 0 = A
n-path {i} {A} (S n) = Σ (n-path {i} {A} n) λ p -> Σ (n-path {i} {A} n) λ q -> p == q

δ : ∀ {i} {A : Type i} -> (n : ℕ) ->
  (n-path {i} {A} (S n)) -> (n-path {i} {A} n) × (n-path {i} {A} n)
δ n p = fst p , fst (snd p)

\end{code}

This is not evidently geometric. To make the connection, we need to use some
facts about equalities of sigma types.

\end{document}
