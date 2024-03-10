/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Odd]
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Even]
    use k
    addarith [hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h1 :=
      calc
        (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
        _ = 0 := by rw [h]
    obtain h3 | h2 := by apply eq_zero_or_eq_zero_of_mul_eq_zero h1
    left
    addarith [h3]
    right
    addarith [h2]
  · intro h
    obtain h3 | h2 := h
    calc
      x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [h3]
      _ = 0 := by numbers
    calc
      x ^ 2 + x - 6 = 2 ^ 2 + 2 - 6 := by rw [h2]
      _ = 0 := by numbers

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have h1 :=
      calc
        (2 * a - 5) ^ 2 = 4 * a ^ 2 - 20 * a + 25 := by ring
        _ = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5 := by rel [h]
        _ = 1 ^ 2 := by ring
    obtain ⟨hl, hr⟩ := abs_le_of_sq_le_sq' h1 (by numbers) -- 0 < 1 := by numbers
    have hl : 2 * 2 ≤ 2 * a := by addarith [hl]
    cancel 2 at hl
    have hr : 2 * a ≤ 2 * 3 := by addarith [hr]
    cancel 2 at hr
    obtain ha | ha := le_or_succ_le a 2
    · left
      apply le_antisymm
      apply ha
      apply hl
    · right
      apply le_antisymm
      apply hr
      apply ha
  · intro h
    obtain h | h := h
    · calc
        a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw [h]
        _ = -1 := by numbers
        _ ≤ -1 := by numbers
    · calc
        a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw [h]
        _ = -1 := by numbers
        _ ≤ -1 := by numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn4 | hn6 := hn2
  · have hn4 : n = 4 := by addarith [hn4]
    use 2
    calc
      n = 4 := by rw [hn4]
      _ = 2 * 2 := by numbers
  · have hn6 : n = 6 := by addarith [hn6]
    use 3
    calc
      n = 6 := by rw [hn6]
      _ = 2 * 3 := by numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain hn4 | hn6 := hn1
  have hn4 : n = 4 := by addarith [hn4]
  · have hn4 : n = 4 := by addarith [hn4]
    use 2
    apply hn4
  · have hn6 : n = 6 := by addarith [hn6]
    use 3
    apply hn6

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    calc
      x = (2 * x - 1 + 1) / 2 := by ring
      _ = (11 + 1) / 2 := by rw [h]
      _ = 6 := by numbers
  · intro h
    calc
      2 * x - 1 = 2 * 6 - 1 := by rw [h]
      _ = 11 := by numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  -- 63 ∣ n → 7 ∣ n ∧ 9 ∣ n
  · intro h
    constructor
    · obtain ⟨k, hk⟩ := h
      use 9 * k
      calc
        n = 63 * k := by rw [hk]
        _ = 7 * (9 * k) := by ring
    · obtain ⟨k, hk⟩ := h
      use 7 * k
      calc
        n = 63 * k := by rw [hk]
        _ = 9 * (7 * k) := by ring
  -- 7 ∣ n ∧ 9 ∣ n → 63 ∣ n
  · intro h
    obtain ⟨⟨a, ha⟩ , ⟨b, hb⟩⟩ := h
    use (4 * a - 5 * b)
    calc
      n = 36 * n - 35 * n := by ring
      _ = 36 * (7 * a) - 35 * n := by rw [ha]
      _ = 36 * (7 * a) - 35 * (9 * b) := by rw [hb]
      _ = 63 * (4 * a - 5 * b) := by ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    use k
    calc
      a - 0 = a := by ring
      _ = n * k := by rw [hk]
  · intro h
    dsimp [Int.ModEq] at h
    obtain ⟨k, hk⟩ := h
    use k
    calc
      a = a - 0 := by ring
      _ = n * k := by rw [hk]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [Int.dvd_iff_modEq] at *
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel [hab]
    _ = 0 := by ring

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  -- k ^ 2 ≤ 6 → k = 0 ∨ k = 1 ∨ k = 2
  · intro h
    have h1 : k ^ 2 < 3 ^ 2 := by
      calc
        k ^ 2 ≤ 6 := by rel [h]
        _ < 6 + 3 := by extra
        _ = 3 ^ 2 := by numbers
    cancel 2 at h1 -- it took too much time to remember i can do this
    interval_cases k
    · left
      numbers
    · right
      left
      numbers
    · right
      right
      numbers

  -- k = 0 ∨ k = 1 ∨ k = 2 → k ^ 2 ≤ 6
  · intro h
    obtain hk | hk | hk := h
    · rw [hk]
      numbers
    · rw [hk]
      numbers
    · rw [hk]
      numbers
