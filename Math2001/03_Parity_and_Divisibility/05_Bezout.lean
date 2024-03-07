/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use (5 * a - 3 * n)
  calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  use 2 * x - n
  calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * x) - 5 * n := by rw [hx]
    _ = 5 * (2 * x - n) := by ring

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨x, hx⟩ := hn
  use (2 * n - x)
  calc
    n = 12 * n - 11 * n := by ring
    _ = 12 * n - (6 * x) := by rw [hx]
    _ = 6 * (2 * n - x) := by ring

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨x, hx⟩ := ha
  use (3 * x - 2 * a)
  calc
    a = 15 * a - 14 * a := by ring
    _ = 3 * (5 * a) - 14 * a := by ring
    _ = 3 * (7 * x) - 14 * a := by rw [hx]
    _ = 7 * (3 * x - 2 * a) := by ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use (4 * a - 5 * b)
  calc
    n = 36 * n - 35 * n := by ring
    _ = 4 * 9 * n - 5 * 7 * n := by ring
    _ = 4 * 9 * (7 * a) - 5 * 7 * n := by rw [ha]
    _ = 4 * 9 * (7 * a) - 5 * 7 * (9 * b) := by rw [hb]
    _ = 63 * (4 * a - 5 * b) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use (2 * a - 5 * b)
  calc
    n = 26 * n - 25 * n := by ring
    _ = 2 * 13 * n - 5 * 5 * n := by ring
    _ = 2 * 13 * (5 * a) - 5 * 5 * n := by rw [ha]
    _ = 2 * 13 * (5 * a) - 5 * 5 * (13 * b) := by rw [hb]
    _ = 65 * (2 * a - 5 * b) := by ring
