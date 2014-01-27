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
\end{code}

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

module Ex2-1 where
  _■₁_ : ∀ {i} {A : Type i} {x y z : A} → (x == y) → (y == z) → (x == z)
  _■₁_ {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → (p : x == y) → Type i
    D x y _ = y == z → x == z

    d : (x : A) → D x x idp
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

      d : (y : A) → D y y idp
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

    d : (x₁ : A) → D x₁ x₁ idp
    d _ = ind== E e where
      E : (x z : A) (q : x == z) → Type i
      E x z _ = x == z

      e : (x : A) → E x x idp
      e _ = idp

\end{code}

We now want to show that these constructions are pairwise equal. By this, we mean ``propositional equality'' - hence we must find paths between each pair of constructions.

\begin{code}

  ■₁=■₂ : ∀ {i} {A : Type i} {x y z : A} 
    (p : x == y) (q : y == z) → p ■₁ q == p ■₂ q
  ■₁=■₂ {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) →  p ■₁ q == p ■₂ q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y₁ z₁ : A) → y₁ == z₁ → Type i
      E _ _ q = idp ■₁ q == idp ■₂ q

      e : (x₁ : A) → E x₁ x₁ idp
      e _ = idp -- : concat1' idp idp == concat2' idp idp   ⇓'p'
                -- > (ind== D1 d1) idp idp == (ind== D2 d2) idp idp 
                -- > (d1 q) idp == (d2 x) idp
                -- > (λ q → q) idp == 'p' (aka idp)
                -- > idp == idp -- (this being the type of the inhabitant value idp of e x)

  ■₂=■₃ : ∀ {i} {A : Type i} {x y z : A} 
    (p : x == y) (q : y == z) →  p ■₂ q == p ■₃ q
  ■₂=■₃ {i} {A} {x} {y} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) → p ■₂ q == p ■₃ q

    d : (x : A) → D x x idp
    d x = ind== E e where
      E : (y₁ z₁ : A) → y₁ == z₁ → Type i
      E _ _ q = idp ■₂ q == idp ■₃ q

      e : (x₁ : A) → E x₁ x₁ idp
      e _ = idp -- : concat2' idp idp == concat3' idp idp


  ■₁=■₃ : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) → p ■₁ q == p ■₃ q
  ■₁=■₃ {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D x y p = (q : y == z) →  p ■₁ q == p ■₃ q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y z : A) → (q : y == z) → Type i
      E _ _ q =  idp ■₁ q == idp ■₃ q

      e : (y : A) → E y y idp
      e _ = idp -- : concat1' idp idp == concat3' idp idp
\end{code}
\end{proof}

\begin{code}
module Ex2-2 where
             
  open Ex2-1
  
  {-
  Show that the three equalities of proofs constructed in the previous exercise form a
  commutative triangle. In other words, if the three definitions of concatenation are denoted
  by (p 1 q), (p 2 q), and (p 3 q), then the concatenated equality
  (p 1 q) = (p 2 q) = (p 3 q)
  is equal to the equality 
  (p 1 q) = (p 3 q).
  -}

  
  -- likewise, the ind== version of the book concat operator
  _■_ = _■₃_

  concat-commutative-triangle' : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) →
    (■₁=■₂ p q) ■ (■₂=■₃ p q) == ■₁=■₃ p q
  concat-commutative-triangle' {i} {A} {_} {_} {z} = ind== D d where
    D : (x y : A) → x == y → Type i
    D _ y p = (q : y == z) → 
      (■₁=■₂ p q) ■ (■₂=■₃ p q) == ■₁=■₃ p q

    d : (x : A) → D x x idp
    d _ = ind== E e where
      E : (y z : A) → (q : y == z) → Type i
      E _ _ q = 
        (■₁=■₂ idp q) ■ (■₂=■₃ idp q) == ■₁=■₃ idp q

      e : (y : A) → E y y idp
      e _ = idp -- : concat' (concat1'=concat2' idp idp) (concat2'=concat3' idp idp) == concat1'=concat3' idp idp
                                                                                                              
module Ex2-3 where
             
  -- use another of the based path inductions
                                   
module Ex2-4 where
             
{- Define, by induction on n, a general notion of n-dimensional path in a type A,
simultaneously with the type of boundaries for such paths. -}


\end{code}

\end{document}
