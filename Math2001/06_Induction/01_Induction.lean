/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    dsimp [Even]
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      dsimp [Odd]
      use x
      rw [hx]
    · left
      use x + 1
      calc
        k + 1 = 2 * x + 1 + 1 := by rw [hx]
        _ = 2 * (x + 1) := by ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · -- base case
    use 0
    ring
  · -- inductive step
    obtain ⟨x, hx⟩ := IH
    obtain ⟨y, hy⟩ := h
    use (a * x + b ^ k * y)
    calc
      a ^ (k + 1) - b ^ (k + 1)
        = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
      _ = a * (d * x) + b ^ k * (d * y) := by rw [hx, hy]
      _ = d * (a * x + b ^ k * y) := by ring

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = k ^ 2 + 2 * k + 1 + 7 := by ring
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc
      3 ^ (k + 1) = 3 ^ k * 3 := by ring
      _ ≥ (k ^ 2 + k + 1) * 3 := by rel [IH]
      _ = (k ^ 2 + 2 * k + 1) + (k + 1) + 1 + 2 * k ^ 2 := by ring
      _ = (k + 1) ^ 2 + (k + 1) + 1 + 2 * k ^ 2 := by ring
      _ ≥ (k + 1) ^ 2 + (k + 1) + 1 := by extra

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · -- base case
    calc
      (1 + a) ^ 0 = 1 := by ring
      _ ≥ 1 := by numbers
      _ = 1 + 0 * a := by ring
  · -- inductive step
    have hap : 0 ≤ 1 + a := by addarith [ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
      _ ≥ (1 + k * a) * (1 + a) := by rel [IH]
      _ = 1 + k * a + a + k * a * a := by ring
      _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hx | hx := IH
    · right
      calc
        5 ^ (k + 1) = 5 ^ k * 5 := by ring
        _ ≡ 1 * 5 [ZMOD 8] := by rel [hx]
        _ = 5 := by numbers
    · left
      calc
        5 ^ (k + 1) = 5 ^ k * 5 := by ring
        _ ≡ 5 * 5 [ZMOD 8] := by rel [hx]
        _ = 1 + 3 * 8 := by numbers
        _ ≡ 1 [ZMOD 8] := by extra

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hx | hx := IH
    · right
      calc
        6 ^ (k + 1) = 6 ^ k * 6 := by ring
        _ ≡ 1 * 6 [ZMOD 7] := by rel [hx]
        _ = 6 := by numbers
    · left
      calc
        6 ^ (k + 1) = 6 ^ k * 6 := by ring
        _ ≡ 6 * 6 [ZMOD 7] := by rel [hx]
        _ = 1 + 5 * 7 := by numbers
        _ ≡ 1 [ZMOD 7] := by extra

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hx | hx | hx := IH
    · right
      right
      calc
        4 ^ (k + 1) = 4 ^ k * 4 := by ring
        _ ≡ 1 * 4 [ZMOD 7] := by rel [hx]
        _ = 4 := by numbers
    · left
      calc
        4 ^ (k + 1) = 4 ^ k * 4 := by ring
        _ ≡ 2 * 4 [ZMOD 7] := by rel [hx]
        _ = 1 + 7 * 1 := by numbers
        _ ≡ 1 [ZMOD 7] := by extra
    . right
      left
      calc
        4 ^ (k + 1) = 4 ^ k * 4 := by ring
        _ ≡ 4 * 4 [ZMOD 7] := by rel [hx]
        _ = 2 + 7 * 2 := by numbers
        _ ≡ 2 [ZMOD 7] := by extra

#eval 3 ^ 5 ≥ 2 * 5 + 100

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      (3 : ℤ) ^ (k + 1) = (3 ^ k) * 3 := by ring
      _ ≥ (2 ^ k + 100) * 3 := by rel [IH]
      _ = 2 * 2 ^ k + 100 + 2 ^ k + 200 := by ring
      _ ≥ 2 * 2 ^ k + 100 + 2 ^ k := by extra -- single "extra" didn't work
      _ ≥ 2 * 2 ^ k + 100 := by extra
      _ = 2 ^ (k + 1) + 100 := by ring

#eval 2 ^ 5 ≥ 5 ^ 2 + 4

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 ^ k * 2 := by ring
      _ ≥ (k ^ 2 + 4) * 2 := by rel [IH]
      _ = k ^ 2 + k * k + 8 := by ring
      _ ≥ k ^ 2 + 5 * k + 8 := by rel [hk]
      _ = (k ^ 2 + 2 * k + 1) + 4 + 3 * k + 3 := by ring
      _ = (k + 1) ^ 2 + 4 + 3 * k + 3 := by ring
      _ ≥ (k + 1) ^ 2 + 4 + 3 * 5 + 3 := by rel [hk]
      _ ≥ (k + 1) ^ 2 + 4 := by extra



example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 ^ k * 2 := by ring
      _ ≥ k ^ 3 * 2 := by rel [IH]
      _ = k ^ 3 + k * k ^ 2 := by ring
      _ ≥ k ^ 3 + 10 * k ^ 2 := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 7 * k * k := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 7 * 10 * k := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * k := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * 10 := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 + 669 := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by extra
      _ = (k + 1) ^ 3 := by ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k IH
  · -- base case
    dsimp [Odd]
    use 0
    numbers
  · -- inductive step
    obtain ⟨l, hl⟩ := ha
    obtain ⟨m, hm⟩ := IH
    dsimp [Odd]
    use 2 * m * l + m + l
    calc
      a ^ (k + 1) = a ^ k * a := by ring
      _ = (2 * m + 1) * (2 * l + 1) := by rw [hm, hl]
      _ = 4 * m * l + 2 * m + 2 * l + 1 := by ring
      _ = 2 * (2 * m * l + m + l) + 1 := by ring

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  obtain he | ho := even_or_odd a
  · apply he
  · have h := Odd.pow ho n
    obtain ⟨h1, _⟩ := Nat.odd_iff_not_even (a ^ n : ℕ)
    have hnote := h1 h
    contradiction -- ha and hnot e
