/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · right
      left
      apply h
    · right
      right
      apply h
  · intro h
    obtain h | h | h := h
    · left
      left
      apply h
    · left
      right
      apply h
    · right
      right
      apply h


example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-2, -1, 2, 3, 4} := by check_equality_of_explicit_sets

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0, 2, 4} := by
  check_equality_of_explicit_sets

example : {1, 2} ∩ {3} = ∅ := by check_equality_of_explicit_sets

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  check_equality_of_explicit_sets

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨k, hk⟩ := hx
  constructor
  · use 5 * k + 3
    calc
      x - 1 = (x - 7) + 6 := by ring
      _ = 10 * k + 6 := by rw [hk]
      _ = 2 * (5 * k + 3) := by ring
  · use 2 * k + 1
    calc
      x - 2 = (x - 7) + 5 := by ring
      _ = 10 * k + 5 := by rw [hk]
      _ = 5 * (2 * k + 1) := by ring

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := hx
  use 5 * m - 3 * k
  calc
    x = 25 * x - 24 * x := by ring
    _ = 5 * 5 * x - 3 * 8 * x := by ring
    _ = 5 * 5 * (8 * m) - 3 * 8 * x := by rw [hm]
    _ = 5 * 5 * (8 * m) - 3 * 8 * (5 * k) := by rw [hk]
    _ = 40 * (5 * m - 3 * k) := by ring

example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro x hx hxx
  obtain h | h := hx
  · obtain ⟨k, hk⟩ := h
    mod_cases hkk : k % 2
    · obtain ⟨m, hm⟩ := hkk
      have h_contr := calc
        1 ≡ x ^ 2 [ZMOD 6] := by rel [hxx]
        _ = (3 * k) ^ 2 := by rw [hk]
        _ = (3 * (k - 0)) ^ 2 := by ring
        _ = (3 * (2 * m)) ^ 2 := by rw [hm]
        _ = 6 * 6 * m ^ 2 := by ring
        _ = 0 + 6 * (6 * m ^ 2) := by ring
        _ ≡ 0 [ZMOD 6] := by extra
      numbers at h_contr
    · obtain ⟨m, hm⟩ := hkk
      have h_contr := calc
        1 ≡ x ^ 2 [ZMOD 6] := by rel [hxx]
        _ = (3 * k) ^ 2 := by rw [hk]
        _ = (3 * (k - 1) + 3) ^ 2 := by ring
        _ = (3 * (2 * m) + 3) ^ 2 := by rw [hm]
        _ = 36 * m ^ 2 + 36 * m + 9 := by ring
        _ = 3 + 6 * (6 * m ^ 2 + 6 * m + 1) := by ring
        _ ≡ 3 [ZMOD 6] := by extra
      numbers at h_contr
  · obtain ⟨k, hk⟩ := h
    mod_cases hkk : k % 3
    · obtain ⟨m, hm⟩ := hkk
      have h_contr := calc
        1 ≡ x ^ 2 [ZMOD 6] := by rel [hxx]
        _ = (2 * k) ^ 2 := by rw [hk]
        _ = (2 * (k - 0)) ^ 2 := by ring
        _ = (2 * (3 * m)) ^ 2 := by rw [hm]
        _ = 6 * 6 * m ^ 2 := by ring
        _ = 0 + 6 * (6 * m ^ 2) := by ring
        _ ≡ 0 [ZMOD 6] := by extra
      numbers at h_contr
    · obtain ⟨m, hm⟩ := hkk
      have h_contr := calc
        1 ≡ x ^ 2 [ZMOD 6] := by rel [hxx]
        _ = (2 * k) ^ 2 := by rw [hk]
        _ = (2 * (k - 1) + 2) ^ 2 := by ring
        _ = (2 * (3 * m) + 2) ^ 2 := by rw [hm]
        _ = 36 * m ^ 2 + 24 * m + 4 := by ring
        _ = 4 + 6 * (6 * m ^ 2 + 4 * m) := by ring
        _ ≡ 4 [ZMOD 6] := by extra
      numbers at h_contr
    · obtain ⟨m, hm⟩ := hkk
      have h_contr := calc
        1 ≡ x ^ 2 [ZMOD 6] := by rel [hxx]
        _ = (2 * k) ^ 2 := by rw [hk]
        _ = (2 * (k - 2) + 4) ^ 2 := by ring
        _ = (2 * (3 * m) + 4) ^ 2 := by rw [hm]
        _ = 36 * m ^ 2 + 48 * m + 16 := by ring
        _ = 4 + 6 * (6 * m ^ 2 + 8 * m + 2) := by ring
        _ ≡ 4 [ZMOD 6] := by extra
      numbers at h_contr

def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  obtain ⟨s1, s2, ⟨hs12, hs1, hs2⟩⟩ := hs
  obtain ⟨t1, t2, ⟨ht12, ht1, ht2⟩⟩ := ht
  dsimp [SizeAtLeastTwo] at hst
  push_neg at hst
  obtain h | (h | h) | (h | h) := hst s1 s2
  · contradiction
  · contradiction
  · obtain h1 | (h1 | h1) | (h1 | h1) := hst t1 t2
    · contradiction
    · use s1, s2, t1
      constructor
      · apply hs12
      · constructor
        · intro h2
          rw [h2] at h
          contradiction
        · constructor
          · intro h2
            rw [← h2] at h1
            contradiction
          · dsimp
            exhaust
    · contradiction
    · use s1, s2, t2
      constructor
      · apply hs12
      · constructor
        · intro h2
          rw [h2] at h
          contradiction
        · constructor
          · intro h2
            rw [← h2] at h1
            contradiction
          · dsimp
            exhaust
    · contradiction
  · contradiction
  · obtain h1 | (h1 | h1) | (h1 | h1) := hst t1 t2
    · contradiction
    · use s1, s2, t1
      constructor
      · apply hs12
      · constructor
        · intro h2
          rw [← h2] at h1
          contradiction
        · constructor
          · intro h2
            rw [h2] at h
            contradiction
          · dsimp
            exhaust
    · contradiction
    · use s1, s2, t2
      constructor
      · apply hs12
      · constructor
        · intro h2
          rw [← h2] at h1
          contradiction
        · constructor
          · intro h2
            rw [h2] at h
            contradiction
          · dsimp
            exhaust
    · contradiction
