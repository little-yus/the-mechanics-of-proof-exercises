/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.ExistsDelaborator
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option push_neg.use_distrib true
set_option pp.unicode.fun true
set_option linter.unusedVariables false
open Function


def h (x : ℝ) : ℝ := 2 * x - 5

example : Bijective h := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro x1 x2 hx
    dsimp [h] at hx
    calc x1 = ((2 * x1 - 5) + 5) / 2 := by ring
      _ = ((2 * x2 - 5) + 5) / 2 := by rw [hx]
      _ = x2 := by ring
  · dsimp [Surjective]
    intro y
    take (y + 5) / 2
    calc h ((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 := by rfl
      _ = y := by ring



def a (t : ℝ) : ℝ := t ^ 3 - t

example : ¬ Bijective a := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  take 0, 1
  constructor
  · calc a 0 = 0 ^ 3 - 0 := by rfl
      _ = 1 ^ 3 - 1 := by numbers
      _ = a 1 := by rfl
  · numbers


inductive Celestial
  | sun
  | moon
  deriving DecidableEq

inductive Subatomic
  | proton
  | neutron
  | electron
  deriving DecidableEq

open Celestial Subatomic


def f : Celestial → Subatomic
  | sun => proton
  | moon => electron


example : ¬ Bijective f := by
  dsimp [Bijective]
  push_neg
  right
  dsimp [Surjective]
  push_neg
  take neutron
  intro x
  cases x
  · decide
  · decide


example {f : X → Y} : Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · -- if `f` is bijective then `∀ y, ∃! x, f x = y`
    intro h y
    obtain ⟨h_inj, h_surj⟩ := h
    obtain ⟨x, hx⟩ := h_surj y
    take x
    dsimp
    constructor
    · apply hx
    · intro x' hx'
      apply h_inj
      calc f x' = y := by rw [hx']
        _ = f x := by rw [hx]
  · -- if `∀ y, ∃! x, f x = y` then `f` is bijective
    intro h
    constructor
    · -- `f` is injective
      intro x1 x2 hx1x2
      obtain ⟨x, hx, hx'⟩ := h (f x1) 
      have hxx1 : x1 = x
      · apply hx'
        rfl
      have hxx2 : x2 = x
      · apply hx'
        rw [hx1x2]
      calc x1 = x := by rw [hxx1]
        _ = x2 := by rw [hxx2]
    · -- `f` is surjective
      intro y
      obtain ⟨x, hx, hx'⟩ := h y
      take x
      apply hx


example : ∀ f : Celestial → Celestial, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf 
  -- show that `f` is surjective
  match h_sun : f sun, h_moon : f moon with
  | sun, sun => 
    have : sun = moon
    · apply hf
      rw [h_sun, h_moon]
    contradiction
  | sun, moon => 
    intro y
    cases y
    · take sun
      apply h_sun
    · take moon
      apply h_moon 
  | moon, sun => sorry
  | moon, moon => sorry


example : ¬ ∀ f : ℕ → ℕ, Injective f → Bijective f := by
  push_neg
  take fun n ↦ n + 1
  constructor
  · -- the function is injective
    intro n1 n2 hn
    addarith [hn] 
  · -- the function is not injective
    dsimp [Bijective]
    push_neg
    right
    -- specifically, it's not surjective
    dsimp [Surjective]
    push_neg
    take 0
    intro n
    extra

/-! # Exercises -/


example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry

example : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry


example : Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  sorry

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  sorry

inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by
  sorry

example : ¬ Bijective e := by
  sorry


example : ∀ f : Subatomic → Subatomic, Injective f → Bijective f := by
  sorry


example : ∀ f : Element → Element, Injective f → Bijective f := by
  sorry
