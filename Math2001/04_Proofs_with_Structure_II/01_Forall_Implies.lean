/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers


example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2 -- for natural number n > 0 <=> n >= 1


example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have hm : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain hm | hm := hm
  calc
    b = 2 * ((a + b) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [hm]
    _ = a := by ring
  calc
    a = 2 * ((a + b) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [hm]
    _ = b := by ring

example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring


example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h
  have h1 :=
    calc
      (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
      _ = 2 * (x ^ 2 + y ^ 2) := by ring
      _ ≤ 2 * 4 := by rel [h]
      _ ≤ 3 ^ 2 := by numbers
  have h3pos : (0 : ℝ) ≤ 3 := by numbers
  obtain ⟨hge3, hle3⟩ := abs_le_of_sq_le_sq' h1 h3pos
  apply hge3

example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp
  use 5
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra


example : Prime 2 := by
  constructor
  · numbers -- show `2 ≤ 2`
  intro m hmp
  have hp : 0 < 2 := by numbers
  have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
  interval_cases m
  · left
    numbers -- show `1 = 1`
  · right
    numbers -- show `2 = 2`


example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- show `2 ≠ 1`
  · numbers -- show `2 ≠ 6`
  · numbers -- show `6 = 2 * 3`

/-! # Exercises -/


example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by apply h
    _ = 1 := by numbers

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h3 : 3 ∣ n
  apply hn
  · numbers
  · numbers
  have h5 : 5 ∣ n
  apply hn
  · numbers
  · numbers
  obtain ⟨a, ha⟩ := h3
  obtain ⟨b, hb⟩ := h5
  use (2 * a - 3 * b)
  calc
    n = 10 * n - 9 * n := by ring
    _ = 10 * (3 * a) - 9 * n := by rw [ha]
    _ = 10 * (3 * a) - 9 * (5 * b) := by rw [hb]
    _ = 15 * (2 * a - 3 * b) := by ring

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  intro m
  extra
  -- "apply Nat.zero_le" also works

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use 1
  intro b
  use b + 2
  calc
    1 + b < 1 + b + 1 := by extra
    _ = b + 2 := by ring

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 10
  intro x hx
  calc
    x ^ 3 + 3 * x
      = x * x ^ 2 + 3 * x := by ring
    _ ≥ 10 * x ^ 2 + 3 * 10 := by rel [hx]
    _ = (7 * x ^ 2 + 12) + (3 * x ^ 2 + 18) := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra

example : ¬(Prime 45) := by
  apply not_prime 5 9
  · numbers
  · numbers
  · numbers
