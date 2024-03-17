/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)


#eval 0 ^ 0 ^ 0 + 1 -- 1
#eval 0 ^ 0 ^ 1 + 1 -- 2
#eval 0 ^ 0 ^ 2 + 1 -- 2


theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  conv at one_prime => numbers -- simplifies that statement to `Prime 1`
  have : ¬ Prime 1 := not_prime_one
  contradiction


#eval 1 ^ 1 ^ 0 + 1 -- 2
#eval 1 ^ 1 ^ 1 + 1 -- 2
#eval 1 ^ 1 ^ 2 + 1 -- 2


theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two


#eval 2 ^ 2 ^ 0 + 1 -- 3
#eval 2 ^ 2 ^ 1 + 1 -- 5
#eval 2 ^ 2 ^ 2 + 1 -- 17
#eval 2 ^ 2 ^ 3 + 1 -- 257
#eval 2 ^ 2 ^ 4 + 1 -- 65537


#eval 3 ^ 3 ^ 0 + 1 -- 4
#eval 3 ^ 3 ^ 1 + 1 -- 28
#eval 3 ^ 3 ^ 2 + 1 -- 19684


theorem not_superpowered_three : ¬ Superpowered 3 := by
  intro h
  dsimp [Superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  conv at four_prime => numbers -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬ Prime 4
  · apply not_prime 2 2
    · numbers -- show `2 ≠ 1`
    · numbers -- show `2 ≠ 4`
    · numbers -- show `4 = 2 * 2`
  contradiction


example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases h2 : Superpowered 2
  · use 2
    constructor
    · apply h2
    · apply not_superpowered_three
  · use 1
    constructor
    · apply superpowered_one
    · apply h2


example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction

/-! # Exercises -/


def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

#eval ((1 : ℚ) + 2/3) ^ 3 < 3 -- 2 is not tribalanced

theorem tribalanced_zero : Tribalanced 0 := by
  intro n
  conv => ring
  numbers

theorem not_tribalanced_two : ¬ Tribalanced 2 := by
  intro h
  dsimp [Tribalanced] at h
  have h1 := h 1
  numbers at h1

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h : Tribalanced 1
  · use 1
    constructor
    · apply h
    · conv => numbers
      apply not_tribalanced_two
  · use 0
    constructor
    · apply tribalanced_zero
    · conv => numbers
      apply h

example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro hpq hq
    by_cases hp : P
    · apply hp
    · have hnq := hpq hp
      contradiction
  · intro hqp hnp
    by_cases hq : Q
    · have hp := hqp hq
      contradiction
    · apply hq

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  · apply superpowered_one
  · conv => numbers
    intro h
    dsimp [Superpowered] at h
    have hprime := h 5
    conv at hprime => numbers
    have hnotprime : ¬ Prime 4294967297
    · apply not_prime 641 6700417
      · numbers
      · numbers
      · numbers
    contradiction -- hprime and hnotprime
