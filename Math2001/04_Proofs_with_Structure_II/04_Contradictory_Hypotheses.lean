/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    have hm_le_p := Nat.le_of_dvd hp' hmp
    obtain hm_eq_p | hm_lt_p := eq_or_lt_of_le hm_le_p
    · right
      apply hm_eq_p
    · have hcontr : ¬ m ∣ p
      apply H
      apply hm_left
      apply hm_lt_p
      contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain ha_le_2 | ha_ge_3 := le_or_succ_le a 2
  · obtain hb_le_1 | hb_ge_2 := le_or_succ_le b 1
    · have hc_lt_3 :=
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha_le_2, hb_le_1]
          _ < 3 ^ 2 := by numbers
      cancel 2 at hc_lt_3
      interval_cases b
      interval_cases a
      · interval_cases c
        · numbers at h_pyth
        · numbers at h_pyth
      · interval_cases c
        · numbers at h_pyth
        · numbers at h_pyth
    · have hb_lt_c :=
        calc
          b ^ 2 < a ^ 2 + b ^ 2 := by extra
          _ = c ^ 2 := by rw [h_pyth]
      cancel 2 at hb_lt_c
      have hb1_le_c : b + 1 ≤ c := by apply hb_lt_c -- I don't understand why this works
      have hc_lt_b1 :=
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + b ^ 2 := by rel [ha_le_2]
          _ = b ^ 2 + 2 * 2 := by ring
          _ ≤ b ^ 2 + 2 * b := by rel [hb_ge_2]
          _ < b ^ 2 + 2 * b + 1 := by extra
          _ = (b + 1) ^ 2 := by ring
      cancel 2 at hc_lt_b1
      have hnot_b1_le_c : ¬ (c < b + 1)
      · apply not_lt_of_ge
        apply hb1_le_c
      contradiction
  · apply ha_ge_3

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  obtain hy_le_x | hx_lt_y := le_or_lt  y x
  · apply hy_le_x
  · have h1 : x ^ n < y ^ n := by rel [hx_lt_y] -- Why?
    have h2 := not_lt_of_ge h
    contradiction

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases hm : n % 5
  · have h :=
      calc
        0 ≡ 0 * 0 [ZMOD 5] := by numbers
        _ ≡ n * n [ZMOD 5] := by rel [hm]
        _ = n ^ 2 := by ring
        _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at h -- contradiction
  · have h :=
      calc
        1 ≡ 1 * 1 [ZMOD 5] := by numbers
        _ ≡ n * n [ZMOD 5] := by rel [hm]
        _ = n ^ 2 := by ring
        _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at h -- contradiction
  · left
    apply hm
  · right
    apply hm
  · have h :=
      calc
        1 ≡ 1 + 5 * 3 [ZMOD 5] := by extra
        _ = 4 * 4 := by numbers
        _ ≡ n * n [ZMOD 5] := by rel [hm]
        _ = n ^ 2 := by ring
        _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at h -- contradiction

example : Prime 7 := by
  apply prime_test
  · numbers
  · intro m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3
      constructor <;> numbers
    · use 2
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h | h := h3
  · have hx_lt_1 : ¬ 1 < x
    apply not_lt_of_ge
    have h :=
      calc
        1 ≥ -2 := by numbers
        _ = (0 : ℚ) - 2 := by ring
        _ = (x + 2) - 2 := by rw [h]
        _ = x := by ring
    apply h
    contradiction
  · addarith [h]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at h
  obtain h1 | h1 := le_or_gt p 2
  -- p ≤ 2 and p ≥ 2 → p = 2
  · obtain ⟨h2, _⟩ := h
    left
    apply le_antisymm
    apply h1
    apply h2
  · obtain h2 | h2 := even_or_odd p
    -- Even p has divisor 2 - contradiction with Prime p
    · dsimp [Even] at h2
      obtain ⟨ha, hprime⟩ := h
      obtain h21 | h2p := hprime 2 h2
      · numbers at h21
      · have hnot : ¬ p > 2
        apply not_lt_of_ge
        calc
          2 ≥ 2 := by numbers
          _ = p := h2p
        contradiction
    -- Odd p - goal
    · right
      apply h2
