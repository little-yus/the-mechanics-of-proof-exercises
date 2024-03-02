/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < x * (-t) :=
      calc
        0 < -x * t := by addarith [hxt]
        _ = x * (-t) := by ring
    cancel x at hxt'
    have ht : t < 0 := by addarith [hxt']
    apply ne_of_lt
    apply ht


example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  have hp : p < (p + q) / 2 := by
    calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  have hq : (p + q) / 2 < q := by
    calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring
  constructor
  apply hp
  apply hq

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1 / 2
  calc
    (x + 1 / 2) ^ 2
      = x + (x ^ 2 + 1 / 4) := by ring
    _ > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hx⟩ := h
  have h1 : (1 - x) * (t - 1) > 0 := by
    calc
      (1 - x) * (t - 1)
        = x + t - (x * t + 1) := by ring
      _ > x * t + 1 - (x * t + 1) := by rel [hx]
      _ = 0 := by ring
  have h2 := le_or_gt x 1
  obtain hx_le_1 | hx_gt_1 := h2
  · have h3 : 1 - x ≥ 0 := by addarith [hx_le_1]
    cancel (1 - x) at h1
    apply ne_of_gt
    addarith [h1]
  · have h3 : (x - 1) * (1 - t) > 0 := by
      calc
        (x - 1) * (1 - t) = (1 - x) * (t - 1) := by ring
        _ > 0 := by rel [h1]
    have h4 : x - 1 > 0 := by addarith [hx_gt_1]
    cancel (x - 1) at h3
    apply ne_of_lt
    addarith [h3]

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hx⟩ := h
  obtain x_le_2 | x_ge_3 := le_or_succ_le x 2
  apply ne_of_lt
  calc
    5 > 2 * 2 := by numbers
    _ ≥ 2 * x := by rel [x_le_2]
    _ = m := by rw [hx]
  apply ne_of_gt
  calc
    m = 2 * x := by rw [hx]
    _ ≥ 2 * 3 := by rel [x_ge_3]
    _ > 5 := by numbers

-- There is probably some elegant solution, but i only managed to prove it by cases
-- Witnesses were selected through trial and error
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain n_le_0 | n_ge_1 := le_or_succ_le n 0
  use 2 -- or any number > 2
  calc
    2 * 2 ^ 3 = 0 * 2 + 7 + 9 := by numbers
    _ ≥ n * 2 + 7 + 9 := by rel [n_le_0]
    _ ≥ n * 2 + 7 := by extra
  use n + 1
  calc
    2 * (n + 1) ^ 3
      = 2 * n ^ 3 + 6 * n ^ 2 + 6 * n + 2 := by ring
    _ = 2 * n ^ 3 + 5 * n ^ 2 + 5 * n + n ^ 2 + n + 2 := by ring
    _ ≥ 2 * 1 ^ 3 + 5 * 1 ^ 2 + 5 * 1 + n ^ 2 + n + 2 := by rel [n_ge_1]
    _ = n ^ 2 + n + 7 + 7 := by ring
    _ ≥ n ^ 2 + n + 7 := by extra
    _ = n * (n + 1) + 7 := by ring

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (-a + b + c) / 2
  use (a - b + c) / 2
  use (a + b - c) / 2
  constructor
  calc
    (-a + b + c) / 2
      = (-a + (b + c)) / 2 := by ring
    _ ≥ (-a + a) / 2 := by rel [ha]
    _ = 0 := by ring
  constructor
  calc
    (a - b + c) / 2
      = (a + c - b) / 2 := by ring
    _ ≥ (b - b) / 2 := by rel [hb]
    _ = 0 := by ring
  constructor
  calc
    (a + b - c) / 2
      ≥ (c - c) / 2 := by rel [hc]
    _ = 0 := by ring
  constructor
  ring
  constructor
  ring
  ring
