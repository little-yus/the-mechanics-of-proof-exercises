/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use (2 * a * b + a + 3 * b + 1)
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use (3 * t - 1)
  calc
    3 * m - 5 = 3 * (2 * t + 1) - 5 := by rw [ht]
    _ = 6 * t + 3 - 5 := by ring
    _ = 2 * (3 * t - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc
    n ^ 2 + 2 * n - 5
      = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw [hk]
    _ = 4 * k ^ 2 + 4 * k - 6 + 1 := by ring
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  dsimp [Odd]
  use -5
  numbers

example : Even (26 : ℤ) := by
  dsimp [Even]
  use 13
  numbers

-- These are easy if you first write out "calc" part, then "use"
example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use a + b
  calc
    n + m = (2 * b) + (2 * a + 1) := by rw [hb, ha]
    _ = 2 * (a + b) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  use a - b - 2
  calc
    p - q - 4 = (2 * a + 1) - (2 * b) - 4 := by rw [ha, hb]
    _ = 2 * (a - b - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  use 3 * c + d - 1
  calc
    3 * a + b - 3 = 3 * (2 * c) + (2 * d + 1) - 3 := by rw [hc, hd]
    _ = 2 * (3 * c + d - 1) := by ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨a, hr⟩ := hr -- we can rewrite hr hypotesis
  obtain ⟨b, hs⟩ := hs
  use (3 * a - 5 * b - 1)
  calc
    3 * r - 5 * s
      = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [hr, hs]
    _ = 2 * (3 * a - 5 * b - 1) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hx⟩ := hx
  use (4 * k ^ 3 + 6 * k ^ 2 + 3 * k)
  calc
    x ^ 3 = (2 * k + 1) ^ 3 := by rw [hx]
    _ = (2 * k) ^ 3 + 3 * (2 * k) ^ 2 + 3 * (2 * k) + 1 := by ring
    _ = 8 * k ^ 3 + 12 * k ^ 2 + 6 * k + 1 := by ring
    _ = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hn⟩ := hn
  use (2 * k ^ 2 - k)
  calc
    n ^ 2 - 3 * n + 2
      = (2 * k + 1) ^ 2 - 3 * (2 * k + 1) + 2 := by rw [hn]
    _ = 4 * k ^ 2 + 4 * k + 1 - 6 * k - 3 + 2 := by ring
    _ = 2 * (2 * k ^ 2 - k) := by ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k, ha⟩ := ha
  use (2 * k ^ 2 + 4 * k - 1)
  calc
    a ^ 2 + 2 * a - 4
      = (2 * k + 1) ^ 2 + 2 * (2 * k + 1) - 4 := by rw [ha]
    _ = 4 * k ^ 2 + 4 * k + 1 + 4 * k + 2 - 4 := by ring
    _ = 2 * (2 * k ^ 2 + 4 * k - 1) + 1 := by ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k, hp⟩ := hp
  use (2 * k ^ 2 + 5 * k - 1)
  calc
    p ^ 2 + 3 * p - 5
      = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw [hp]
    _ = 4 * k ^ 2 + 4 * k + 1 + 6 * k + 3 - 5 := by ring
    _ = 2 * (2 * k ^ 2 + 5 * k - 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a, hx⟩ := hx
  obtain ⟨b, hy⟩ := hy
  use (2 * a * b + a + b)
  calc
    x * y = (2 * a + 1) * (2 * b + 1) := by rw [hx, hy]
    _ = 4 * a * b + 2 * a + 2 * b + 1 := by ring
    _ = 2 * (2 * a * b + a + b) + 1 := by ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn_even | hn_odd := Int.even_or_odd n
  · obtain ⟨k, hn_even⟩ := hn_even
    use (6 * k ^ 2 + 3 * k - 1)
    calc
      3 * n ^ 2 + 3 * n - 1
        = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hn_even]
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring
  · obtain ⟨k, hn_odd⟩ := hn_odd
    use (6 * k ^ 2 + 9 * k + 2)
    calc
      3 * n ^ 2 + 3 * n - 1
        = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hn_odd]
      _ = 3 * (4 * k ^ 2 + 4 * k + 1) + 6 * k + 3 - 1 := by ring
      _ = 12 * k ^ 2 + 18 * k + 5 := by ring
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn_even | hn_odd := Int.even_or_odd n
  · obtain ⟨k, hn_even⟩ := hn_even
    use n + 1
    constructor
    extra
    use k
    rw [hn_even]
  · obtain ⟨k, hn_odd⟩ := hn_odd
    use n + 2
    constructor
    extra
    use k + 1
    calc
      n + 2 = 2 * k + 1 + 2 := by rw [hn_odd]
      _ = 2 * (k + 1) + 1 := by ring

-- "elegant" solution using 6 cases
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha_even | ha_odd := Int.even_or_odd a
  · obtain ⟨k, ha_even⟩ := ha_even
    obtain hb_even | hb_odd := Int.even_or_odd b
    · obtain ⟨l, hb_even⟩ := hb_even
      left
      use k - l
      calc
        a - b = 2 * k - 2 * l := by rw[ha_even, hb_even]
        _ = 2 * (k - l) := by ring

    · obtain ⟨l, hb_odd⟩ := hb_odd
      obtain hc_even | hc_odd := Int.even_or_odd c
      · obtain ⟨m, hc_even⟩ := hc_even
        right
        left
        use k + m
        calc
          a + c = 2 * k + 2 * m := by rw [ha_even, hc_even]
          _ = 2 * (k + m) := by ring

      · obtain ⟨m, hc_odd⟩ := hc_odd
        right
        right
        use l - m
        calc
          b - c = (2 * l + 1) - (2 * m + 1) := by rw [hb_odd, hc_odd]
          _ = 2 * (l - m) := by ring

  · obtain ⟨k, ha_odd⟩ := ha_odd
    obtain hb_even | hb_odd := Int.even_or_odd b
    · obtain ⟨l, hb_even⟩ := hb_even
      obtain hc_even | hc_odd := Int.even_or_odd c
      · obtain ⟨m, hc_even⟩ := hc_even
        right
        right
        use l - m
        calc
          b - c = (2 * l) - (2 * m) := by rw [hb_even, hc_even]
          _ = 2 * (l - m) := by ring

      · obtain ⟨m, hc_odd⟩ := hc_odd
        right
        left
        use k + m + 1
        calc
          a + c = (2 * k + 1) + (2 * m + 1) := by rw [ha_odd, hc_odd]
          _ = 2 * (k + m + 1) := by ring

    · obtain ⟨l, hb_odd⟩ := hb_odd
      left
      use k - l
      calc
        a - b = (2 * k + 1) - (2 * l + 1) := by rw [ha_odd, hb_odd]
        _ = 2 * (k - l) := by ring
