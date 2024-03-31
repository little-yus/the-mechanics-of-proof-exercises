/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := lt_fmod_of_neg (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := lt_fmod_of_neg (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have hd0 : 0 < -d := by addarith [hd]
    have h : -d * (n - d) ≥ 0 := by addarith [h2]
    cancel -d at h
    have h : d ≤ n := by addarith [h]
    apply lt_of_le_of_ne
    · apply h
    · apply Ne.symm -- using lemmas not mentioned in the book feels like cheating
      apply h3
termination_by _ n d hd => 2 * n - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  · have IH := T_eq (1 - n)
    calc
      T (1 - n) + 2 * n - 1 = (1 - n) ^ 2 + 2 * n - 1 := by rw [IH]
      _ = n ^ 2 := by ring
  · have IH := T_eq (-n)
    calc
      T (-n) = (-n) ^ 2 := by rw [IH]
      _ = n ^ 2 := by ring
  · have h2 : 0 ≤ n := by addarith [h2]
    have hn0 : n = 0
    apply le_antisymm
    · apply h1
    · apply h2
    rw [hn0]
    numbers
termination_by _ n => 3 * n - 1 -- I don't like that this thing is not explained properly

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨h1, h2, k, hk⟩ := hr
  obtain ⟨h3, h4, m, hm⟩ := hs
  have hk : r = a - b * k := by addarith [hk]
  have hm : s = a - b * m := by addarith [hm]
  have hrs :=
  calc
    r - s = (a - b * k) - (a - b * m) := by rw [hk, hm]
    _ = b * (m - k) := by ring
  obtain hz | hz := lt_or_ge (r - s) 0
  · have hz : s - r > 0 := by addarith [hz]
    have hrs : s - r = b * (k - m) :=
    calc
      s - r = - (r - s) := by ring
      _ = - (b * (m - k)) := by rw [hrs]
      _ = b * (k - m) := by ring
    have hb : b ∣ (s - r)
    · use (k - m)
      apply hrs
    have hb := Int.le_of_dvd hz hb
    have h5 : s - r < b - r := by addarith [h4]
    have hb1 :=
      calc
        b ≤ s - r := by rel [hb]
        _ < b - r := by rel [h5]
    have hr0 : r < 0 := by addarith [hb1]
    have hr0_contr : ¬ (r < 0) := not_lt_of_ge h1
    contradiction -- hr0 and hr0_contr
  obtain hz1 | hz1 := lt_or_ge 0 (r - s)
  · have hb : b ∣ (r - s)
    · use (m - k)
      apply hrs
    have hb := Int.le_of_dvd hz1 hb
    have h5 : r - s < b - s := by addarith [h2]
    have hb1 :=
      calc
        b ≤ r - s := by rel [hb]
        _ < b - s := by rel [h5] -- by rel [h2] didn't work
    have hs0 : s < 0 := by addarith [hb1]
    have hs0_contr : ¬ (s < 0) := not_lt_of_ge h3
    contradiction -- hs0 and hs_contr
  · apply le_antisymm
    · addarith [hz1]
    · addarith [hz]

example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  dsimp
  constructor
  · constructor
    · apply fmod_nonneg_of_pos
      apply h
    · constructor
      · apply fmod_lt_of_pos
        apply h
      · use fdiv a b
        have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
        addarith [Hab]
  · intro y hy
    apply uniqueness
    · apply h
    · apply hy
    · constructor
      · apply fmod_nonneg_of_pos
        apply h
      · constructor
        · apply fmod_lt_of_pos
          apply h
        · use fdiv a b
          have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
          addarith [Hab]
