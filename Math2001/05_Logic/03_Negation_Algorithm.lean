/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h
    intro hpq
    obtain hnp | hnq := h
    · obtain ⟨hp, _⟩ := hpq
      contradiction
    · obtain ⟨_, hq⟩ := hpq
      contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
  _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
  _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m) ∨ ¬(m < (n + 1) ^ 2) := by rel [not_and_or]
  _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by rel [not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2 ^ 2 := by numbers
      _ ≤ n ^ 2 := by rel [hn]

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · by_cases hp : P
    · intro h
      apply hp
    · intro h
      contradiction
  · by_cases hp : ¬P
    · intro hp1
      contradiction
    · intro hp1
      apply hp

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro hpq
    by_cases hp : P
    · by_cases hq : Q
      · have h : P → Q
        intro
        apply hq
        contradiction
      · constructor
        · apply hp
        · apply hq
    -- I don't understand why this is legal
    · have h : P → Q
      intro hp1
      contradiction
      contradiction
  · intro h
    obtain ⟨hp, hnq⟩ := h
    intro h1
    have hq := h1 hp
    contradiction -- hq and hnq

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · -- To prove this case, I used some similarities it shares with 5.1.6 and a lot of trial and error
    intro ha
    by_cases h : ∃ x, ¬P x
    · apply h
    · have h1 : (¬∃ (x : α), ¬P x) → ∀ (x : α), P x
      intro _ x
      by_cases h2 : P x -- so much work to get x out of a quantified proposition, there has to be a better way
      · apply h2
      · have h3 : ∃ (x : α), ¬P x
        use x
        apply h2
        contradiction -- h and h3
      have h_contr := h1 h
      contradiction -- h_contr and ha
  · intro he ha
    obtain ⟨x, hx⟩ := he
    have hx_contr := ha x
    contradiction -- hx and hx_contr

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc ¬ (∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ ∃ a, ¬∀ b : ℤ, a * b = 1 → a = 1 ∨ b = 1 := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, ¬(a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬(a = 1 ∨ b = 1) := by rel [not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by rel [not_or]

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
      ↔ ∀ x : ℝ, ¬(∀ y : ℝ, y ≤ x) := by rel [not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬(y ≤ x) := by rel [not_forall]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, y > x := by rel [not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
      ↔ ∀ m : ℤ, ¬(∀ n : ℤ, m = n + 5) := by rel [not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel [not_forall]

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  obtain ht | ht := lt_or_ge t 5
  · right
    apply ht
  · left
    calc
      4 < 5 := by numbers
      _ ≤ t := ht

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  obtain hk | hk := le_or_succ_le k 3
  · apply ne_of_gt
    calc
      2 * k ≤ 2 * 3 := by rel [hk]
      _ < 7 := by numbers
  · apply ne_of_lt
    calc
      7 < 2 * 4 := by numbers
      _ ≤ 2 * k := by rel [hk]

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  · apply hk
  · constructor
    · apply hk1
    · apply hkp

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * a ^ 2
  calc
    2 * a ^ 3 = 2 * a ^ 2 * a := by ring
    _ < 2 * a ^ 2 * a + 7 := by extra

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have hp_contr : Prime p
    apply prime_test
    apply hp2
    apply H
    contradiction -- hp and hp_contr
  push_neg at H
  apply H
