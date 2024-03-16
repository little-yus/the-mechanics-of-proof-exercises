/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩ := h
  obtain h1 | h1 := le_or_succ_le n 1
  · have h2 := calc
      2 = n ^ 2 := by rw [hn]
      _ ≤ 1 ^ 2 := by rel [h1]
      _ = 1 := by numbers
    numbers at h2
  · have h2 := calc
      2 = n ^ 2 := by rw [hn]
      _ ≥ 2 ^ 2 := by rel [h1]
      _ = 4 := by numbers
    numbers at h2

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro ho he
    rw [Int.even_iff_modEq] at he
    rw [Int.odd_iff_modEq] at ho
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [he]
      _ ≡ 1 [ZMOD 2] := by rel [ho]
    numbers at h -- contradiction!
  · intro he
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) ≡ 1 + 3 * 1 [ZMOD 3] := by extra
      _ = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    -- Got a bit confused by this, because I forgot that minus will transform < into > in hq₁
    --_ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ < a - b * q := by rel [hq₁]
    _ < b * (q + 1) - b * q := by rel [hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 :=
  calc b * q < a := by rel [hq₁]
    _ = b * k := by rw [hk]
  cancel b at h2
  have h2 : q + 1 ≤ k := h2
  have hcontr : ¬ k < q + 1
  apply not_lt_of_ge
  apply h2
  contradiction -- h1 and hcontr

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    calc
      p = m * l := hl
      _ = l * m := by ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have hlt := calc
      T * l ≤ m * l := by rel [hmT]
      _ = p := by rw [hl]
      _ < T ^ 2 := by rel [hTp]
      _ = T * T := by ring
    cancel T at hlt
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t, h1, h2⟩ := h
  have h1 : t < 5 :=
    calc
      t ≤ 4 := h1
      _ < 5 := by numbers
  have h2 := not_lt_of_ge h2
  contradiction

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro H
  obtain ⟨a, h1, h2⟩ := H
  obtain h0 | h0 := lt_or_le a 0
  · have h0 : -a > 0 := by addarith [h0]
    have ha := calc
      -a ^ 3 = (-a) ^ 3 := by ring
      _ > 0 ^ 3 := by rel [h0]
      _ = 0 := by numbers
    have ha : a ^ 3 < 0 := by addarith [ha]
    have ha : a ^ 3 < 30 :=
      calc
        a ^ 3 < 0 := ha
        _ < 30 := by numbers
    have ha_contr := not_lt_of_ge h2
    contradiction -- ha and ha_contr
  obtain h3 | h3 := le_or_lt a 3
  · have ha :=
      calc
        a ^ 3 ≤ 3 ^ 3 := by rel [h3]
        _ < 30 := by numbers
    have ha_contr := not_lt_of_ge h2
    contradiction -- ha and ha_contr
  · have ha :=
      calc
        a ^ 2 > 3 ^ 2 := by rel [h3]
        _ > 8 := by numbers
    have ha_contr := not_lt_of_ge h1
    contradiction -- ha and ha_contr

example : ¬ Int.Even 7 := by
  intro h
  obtain ⟨k, hk⟩ := h
  have h : (2 : ℤ) ∣ 7
  · use k
    apply hk
  have h_contr : ¬ (2 : ℤ) ∣ 7
  · apply Int.not_dvd_of_exists_lt_and_lt 7 2
    use 3
    constructor
    · numbers
    · numbers
  contradiction

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro H
  obtain ⟨h1, h2⟩ := H
  have h3 :=
    calc
      n ^ 2 = (n + 3 - 3) ^ 2 := by ring
      _ = (7 - 3) ^ 2 := by rw [hn]
      _ = 16 := by numbers
  have h_contr :=
    calc
      10 = n ^ 2 := by rw [h2]
      _ = 16 := by rw [h3]
  numbers at h_contr -- contradiction 10 = 16

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro H
  obtain h | h := H
  · have hmx : -x ≥ 3 := by addarith [h]
    have hx_contr :=
      calc
        x ^ 2 = -x * -x := by ring
        _ ≥ 3 * 3 := by rel [hmx]
        _ = 9 := by numbers
    have hx_contr := not_lt_of_ge hx_contr
    contradiction -- hx and hx_contr
  · have hx_contr :=
      calc
        x ^ 2 = x * x := by ring
        _ ≥ 3 * 3 := by rel [h]
        _ = 9 := by numbers
    have hx_contr := not_lt_of_ge hx_contr
    contradiction -- hx and hx_contr

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro H
  obtain ⟨N, hN⟩ := H
  obtain hNeven | hNodd := Nat.even_or_odd N
  -- Even N ∧ Even (N + 1) leads to contradiction
  · have hN1even := hN (N + 1) (by extra)
    have hN1odd : Nat.Odd (N + 1)
    · obtain ⟨a, ha⟩ := hNeven
      dsimp [Nat.Odd]
      use a
      have h := calc
        N + 1 = (2 * a) + 1 := by rw [ha]
        _ = 2 * a + 1 := by ring
      apply h
    obtain ⟨h, _⟩ := Nat.even_iff_not_odd (N + 1)
    have hN1notodd := h hN1even
    contradiction -- hN1odd and hN1notodd
  -- Odd N ∧ Even (N + 2) leads to contradiction
  · have hN2even := hN (N + 2) (by extra)
    have hN2odd : Nat.Odd (N + 2)
    · obtain ⟨a, ha⟩ := hNodd
      dsimp [Nat.Odd]
      use a + 1
      calc
        N + 2 = 2 * a + 1 + 2 := by rw [ha]
        _ = 2 * (a + 1) + 1 := by ring
    obtain ⟨h, _⟩ := Nat.even_iff_not_odd (N + 2)
    have hN2notodd := h hN2even
    contradiction -- hN2odd and hN2notodd

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro H
  mod_cases hn : n % 4
  · have h := calc
      0 = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h
  · have h := calc
      1 = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h
  · have h := calc
      0 ≡ 0 + 4 * 1 [ZMOD 4] := by extra
      _ = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h
  · have h := calc
      1 ≡ 1 + 4 * 2 [ZMOD 4] := by extra
      _ = 3 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h

example : ¬ Prime 1 := by
  intro h
  dsimp [Prime] at h
  obtain ⟨h1, h2⟩ := h
  numbers at h1

example : Prime 97 := by
  apply better_prime_test (T := 10)
  · numbers
  · numbers
  · intro m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 48
      constructor <;> numbers
    · use 32
      constructor <;> numbers
    · use 24
      constructor <;> numbers
    · use 19
      constructor <;> numbers
    · use 16
      constructor <;> numbers
    · use 13
      constructor <;> numbers
    · use 12
      constructor <;> numbers
    · use 10
      constructor <;> numbers
