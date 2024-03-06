/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


example : 11 ≡ 3 [ZMOD 4] := by
  use 2
  numbers

example : -5 ≡ 1 [ZMOD 3] := by
  dsimp [Int.ModEq]
  dsimp [Dvd.dvd]
  use -2
  numbers

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring


theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  dsimp [Dvd.dvd]
  use (x - y)
  calc
    (a - c) - (b - d)
      = (a - b) - (c - d) := by ring
    _ = n * x - n * y := by rw [hx, hy]
    _ = n * (x - y) := by ring

theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  use -x
  calc
    -a - (-b) = -(a - b) := by ring
    _ = - (n * x) := by rw [hx]
    _ = n * (-x) := by ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring


theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring


theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a ^ 2 + a * b + b ^ 2)
  calc
    a ^ 3 - b ^ 3
      = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = n * x * (a ^ 2 + a * b + b ^ 2) := by rw [hx]
    _ = n * (x * (a ^ 2 + a * b + b ^ 2)) := by ring


theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] :=
  sorry -- we'll prove this later in the book


theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := ha
  use x * (b ^ 2 + a * b + 2 * b + 3)
  calc
    a * b ^ 2 + a ^ 2 * b + 3 * a - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2) =
        (a - 2) * (b ^ 2 + a * b + 2 * b + 3) :=
      by ring
    _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
    _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.pow
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply ha

/-! # Exercises -/


example : 34 ≡ 104 [ZMOD 5] := by
  dsimp [Int.ModEq]
  dsimp [Dvd.dvd]
  use -14
  numbers

theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  dsimp [Int.ModEq]
  obtain ⟨x, hx⟩ := h
  use -x
  calc
    b - a = -(a - b) := by ring
    _ = -(n * x) := by rw [hx]
    _ = n * -x := by ring

theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use (x + y)
  calc
    a - c = (a - b) + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

example : a + n * c ≡ a [ZMOD n] := by
  dsimp [Int.ModEq]
  use c
  ring

-- 6.a
example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  obtain ⟨x, hx⟩ := h
  dsimp [Int.ModEq]
  use (2 * x)
  calc
    2 * a + 3 - (2 * b + 3)
      = 2 * (a - b) := by ring
    _ = 2 * (5 * x) := by rw [hx]
    _ = 5 * (2 * x) := by ring

-- 6.b
example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply h
  apply Int.ModEq.refl

-- 7.a
example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := h
  use (3 * x)
  calc
    3 * m - 1 - (3 * n - 1)
      = 3 * (m - n) := by ring
    _ = 3 * (4 * x) := by rw [hx]
    _ = 4 * (3 * x) := by ring

-- 7.b
example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  apply Int.ModEq.sub
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply h
  apply Int.ModEq.refl

-- 8.a
example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  obtain ⟨x, hx⟩ := hb
  use x * (k ^ 2 + 3 * k + 13)
  calc
    (4 * k + k ^ 3 + 3) - (4 * 3 + 3 ^ 3 + 3)
      = 4 * (k - 3) + (k - 3) * (k ^ 2 + 3 * k + 9) := by ring
    _ = (k - 3) * (k ^ 2 + 3 * k + 13) := by ring
    _ = 5 * x * (k ^ 2 + 3 * k + 13) := by rw [hx]
    _ = 5 * (x * (k ^ 2 + 3 * k + 13)) := by ring

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply hb
  apply Int.ModEq.pow_three
  apply hb
  apply Int.ModEq.refl
