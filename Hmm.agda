{-# OPTIONS --without-K #-}

module Hmm where

  -- using the HoTT-Agda library leads to highlighting error (missing metadata)
  -- open import lib.Base
  -- open import lib.types.Nat

  -- using these libraries does not, yet the code is copied/pasted from HoTT-Agda
  open import Path
  open import Nat

  S= : {m n : ℕ} → m == n → S m == S n
  S= idp = idp

