/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function


def p (x : ℝ) : ℝ := 2 * x - 5

example : Bijective p := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro x1 x2 hx
    dsimp [p] at hx
    calc x1 = ((2 * x1 - 5) + 5) / 2 := by ring
      _ = ((2 * x2 - 5) + 5) / 2 := by rw [hx]
      _ = x2 := by ring
  · dsimp [Surjective]
    intro y
    use (y + 5) / 2
    calc p ((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 := by rfl
      _ = y := by ring



def a (t : ℝ) : ℝ := t ^ 3 - t

example : ¬ Bijective a := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use 0, 1
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
  use neutron
  intro x
  cases x <;> exhaust


example {f : X → Y} : Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · -- if `f` is bijective then `∀ y, ∃! x, f x = y`
    intro h y
    obtain ⟨h_inj, h_surj⟩ := h
    obtain ⟨x, hx⟩ := h_surj y
    use x
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
      use x
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
    · use sun
      apply h_sun
    · use moon
      apply h_moon
  | moon, sun =>
    intro y
    cases y
    · use moon
      apply h_moon
    · use sun
      apply h_sun
  | moon, moon =>
    have : sun = moon
    · apply hf
      rw [h_sun, h_moon]
    contradiction



example : ¬ ∀ f : ℕ → ℕ, Injective f → Bijective f := by
  push_neg
  use fun n ↦ n + 1
  constructor
  · -- the function is injective
    intro n1 n2 hn
    addarith [hn]
  · -- the function is not bijective
    dsimp [Bijective]
    push_neg
    right
    -- specifically, it's not surjective
    dsimp [Surjective]
    push_neg
    use 0
    intro n
    apply ne_of_gt
    extra

/-! # Exercises -/


-- Exercise 1
example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  · intro x1 x2 hf
    dsimp at hf
    have h : 3 * x1 = 3 * x2 := by addarith [hf]
    cancel 3 at h
  · intro y
    use (4 - y) / 3
    dsimp
    ring

-- This one is wrong
-- example : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
--   sorry


-- Exercise 2
-- This one is wrong
-- example : Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
--   sorry

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use 0, -2
  constructor
  · numbers
  · numbers

-- Exercise 3
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
  constructor
  · intro x1 x2 hx
    cases x1 <;> cases x2 <;> exhaust
  · intro y
    cases y
    · use earth
      dsimp [e]
    · use air
      dsimp [e]
    · use fire
      dsimp [e]
    · use water
      dsimp [e]

-- This one is wrong
-- example : ¬ Bijective e := by
--   sorry


-- Exercise 4
-- There are 3 ^ 3 = 27 cases to check
example : ∀ f : Subatomic → Subatomic, Injective f → Bijective f := by
  intro f f_inj
  constructor
  · apply f_inj
  · intro y
    dsimp [Injective] at f_inj
    match h_pt : f proton, h_nt : f neutron, h_el : f electron with
    | proton, neutron, electron =>
      cases y
      · use proton
        apply h_pt
      · use neutron
        apply h_nt
      · use electron
        apply h_el
    | proton, electron, neutron =>
      cases y
      · use proton
        apply h_pt
      · use electron
        apply h_el
      · use neutron
        apply h_nt
    | neutron, proton, electron =>
      cases y
      · use neutron
        apply h_nt
      · use proton
        apply h_pt
      · use electron
        apply h_el
    | neutron, electron, proton =>
      cases y
      · use electron
        apply h_el
      · use proton
        apply h_pt
      · use neutron
        apply h_nt
    | electron, proton, neutron =>
      cases y
      · use neutron
        apply h_nt
      · use electron
        apply h_el
      · use proton
        apply h_pt
    | electron, neutron, proton =>
      cases y
      · use electron
        apply h_el
      · use neutron
        apply h_nt
      · use proton
        apply h_pt

    | electron, electron, _
    | proton, proton, _
    | neutron, neutron, _ =>
      have h : proton = neutron
      · apply f_inj
        rw [h_pt, h_nt]
      contradiction
    | electron, _, electron
    | proton, _, proton
    | neutron, _, neutron =>
      have h : proton = electron
      · apply f_inj
        rw [h_pt, h_el]
      contradiction
    | _, electron, electron
    | _, proton, proton
    | _, neutron, neutron =>
      have h : neutron = electron
      · apply f_inj
        rw [h_nt, h_el]
      contradiction

-- Exercise 5
-- 4 ^ 4 = 64 cases
example : ∀ f : Element → Element, Injective f → Bijective f := by
  intro f f_inj
  constructor
  · apply f_inj
  · dsimp [Injective] at f_inj
    match hf : f fire, hw : f water, he : f earth, ha : f air with
    | fire, water, earth, air =>
      intro y
      cases y
      · use fire
        apply hf
      · use water
        apply hw
      · use earth
        apply he
      · use air
        apply ha
    | fire, water, air, earth =>
      intro y
      cases y
      · use fire
        apply hf
      · use water
        apply hw
      · use air
        apply ha
      · use earth
        apply he
    | fire, earth, water, air =>
      intro y
      cases y
      · use fire
        apply hf
      · use earth
        apply he
      · use water
        apply hw
      · use air
        apply ha
    | fire, earth, air, water =>
      intro y
      cases y
      · use fire
        apply hf
      · use air
        apply ha
      · use water
        apply hw
      · use earth
        apply he
    | fire, air, water, earth =>
      intro y
      cases y
      · use fire
        apply hf
      · use earth
        apply he
      · use air
        apply ha
      · use water
        apply hw
    | fire, air, earth, water =>
      intro y
      cases y
      · use fire
        apply hf
      · use air
        apply ha
      · use earth
        apply he
      · use water
        apply hw

    | water, fire, earth, air =>
      intro y
      cases y
      · use water
        apply hw
      · use fire
        apply hf
      · use earth
        apply he
      · use air
        apply ha
    | water, fire, air, earth =>
      intro y
      cases y
      · use water
        apply hw
      · use fire
        apply hf
      · use air
        apply ha
      · use earth
        apply he
    | water, earth, fire, air =>
      intro y
      cases y
      · use earth
        apply he
      · use fire
        apply hf
      · use water
        apply hw
      · use air
        apply ha
    | water, earth, air, fire =>
      intro y
      cases y
      · use air
        apply ha
      · use fire
        apply hf
      · use water
        apply hw
      · use earth
        apply he
    | water, air, fire, earth =>
      intro y
      cases y
      · use earth
        apply he
      · use fire
        apply hf
      · use air
        apply ha
      · use water
        apply hw
    | water, air, earth, fire =>
      intro y
      cases y
      · use air
        apply ha
      · use fire
        apply hf
      · use earth
        apply he
      · use water
        apply hw

    | earth, fire, water, air =>
      intro y
      cases y
      · use water
        apply hw
      · use earth
        apply he
      · use fire
        apply hf
      · use air
        apply ha
    | earth, fire, air, water =>
      intro y
      cases y
      · use water
        apply hw
      · use air
        apply ha
      · use fire
        apply hf
      · use earth
        apply he
    | earth, water, fire, air =>
      intro y
      cases y
      · use earth
        apply he
      · use water
        apply hw
      · use fire
        apply hf
      · use air
        apply ha
    | earth, water, air, fire =>
      intro y
      cases y
      · use air
        apply ha
      · use water
        apply hw
      · use fire
        apply hf
      · use earth
        apply he
    | earth, air, fire, water =>
      intro y
      cases y
      · use earth
        apply he
      · use air
        apply ha
      · use fire
        apply hf
      · use water
        apply hw
    | earth, air, water, fire =>
      intro y
      cases y
      · use air
        apply ha
      · use earth
        apply he
      · use fire
        apply hf
      · use water
        apply hw

    | air, fire, water, earth =>
      intro y
      cases y
      · use water
        apply hw
      · use earth
        apply he
      · use air
        apply ha
      · use fire
        apply hf
    | air, fire, earth, water =>
      intro y
      cases y
      · use water
        apply hw
      · use air
        apply ha
      · use earth
        apply he
      · use fire
        apply hf
    | air, water, fire, earth =>
      intro y
      cases y
      · use earth
        apply he
      · use water
        apply hw
      · use air
        apply ha
      · use fire
        apply hf
    | air, water, earth, fire =>
      intro y
      cases y
      · use air
        apply ha
      · use water
        apply hw
      · use earth
        apply he
      · use fire
        apply hf
    | air, earth, fire, water =>
      intro y
      cases y
      · use earth
        apply he
      · use air
        apply ha
      · use water
        apply hw
      · use fire
        apply hf
    | air, earth, water, fire =>
      intro y
      cases y
      · use air
        apply ha
      · use earth
        apply he
      · use water
        apply hw
      · use fire
        apply hf

    | fire, fire, _, _
    | water, water, _, _
    | earth, earth, _, _
    | air, air, _, _ =>
      have h : fire = water
      · apply f_inj
        rw [hf, hw]
      contradiction
    | fire, _, fire, _
    | water, _, water, _
    | earth, _, earth, _
    | air, _, air, _ =>
      have h : fire = earth
      · apply f_inj
        rw [hf, he]
      contradiction
    | fire, _, _, fire
    | water, _, _, water
    | earth, _, _, earth
    | air, _, _, air =>
      have h : fire = air
      · apply f_inj
        rw [hf, ha]
      contradiction
    | _, fire, fire, _
    | _, water, water, _
    | _, earth, earth, _
    | _, air, air, _ =>
      have h : water = earth
      · apply f_inj
        rw [hw, he]
      contradiction
    | _, fire, _, fire
    | _, water, _, water
    | _, earth, _, earth
    | _, air, _, air =>
      have h : water = air
      · apply f_inj
        rw [hw, ha]
      contradiction
    | _, _, fire, fire
    | _, _, water, water
    | _, _, earth, earth
    | _, _, air, air =>
      have h : earth = air
      · apply f_inj
        rw [he, ha]
      contradiction

-- That was tedious, i hope i didn't miss some way to automate it
