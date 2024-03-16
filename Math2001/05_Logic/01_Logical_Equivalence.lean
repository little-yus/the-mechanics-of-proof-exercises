/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)

#truth_table P ↔ (¬P ∨ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain ⟨hp, hq⟩ | ⟨hp, hr⟩ := h
    · constructor
      · apply hp
      · left
        apply hq
    · constructor
      · apply hp
      · right
        apply hr

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hp, hq⟩ := h
  left
  apply hp

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1
    apply h3
  · apply h2
    apply h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨hp, hp'⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro hp
  obtain ⟨hnotq_of_p, _⟩ := h1
  have hq' := hnotq_of_p hp
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain hp | hq := h1
  · apply hp
  · apply h2
    apply hq

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨hpq, hqp⟩ := h
  constructor
  · intro hpr
    obtain ⟨hp, hr⟩ := hpr
    constructor
    · apply hpq
      apply hp
    · apply hr
  · intro hqr
    obtain ⟨hq, hr⟩ := hqr
    constructor
    · apply hqp
      apply hq
    · apply hr

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro h
    obtain ⟨hp, _⟩ := h
    apply hp
  · intro hp
    constructor
    · apply hp
    · apply hp

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro hpq
    obtain hp | hq := hpq
    · right
      apply hp
    . left
      apply hq
  · intro hqp
    obtain hq | hp := hqp
    · right
      apply hq
    · left
      apply hp

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro hnpq
    constructor
    · intro hp
      have hpq : P ∨ Q
      left
      apply hp
      contradiction
    · intro hq
      have hpq : P ∨ Q
      right
      apply hq
      contradiction
  · intro hnpnq
    obtain ⟨hnp, hnq⟩ := hnpnq
    intro hporq
    obtain hp | hq := hporq
    · contradiction
    · contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1
  apply h2

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro hp
    have ⟨x, hx⟩ := hp
    obtain ⟨hpq, _⟩ := h x
    use x
    apply hpq
    apply hx
  · intro hq
    have ⟨x, hx⟩ := hq
    obtain ⟨_, hqp⟩ := h x
    use x
    apply hqp
    apply hx

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x, y, hp⟩ := h
    use y, x
    apply hp
  · intro h
    obtain ⟨y, x, hp⟩ := h
    use x, y
    apply hp

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro hp y x
    apply hp
  · intro hp x y
    apply hp

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    obtain ⟨⟨x, hp⟩, hq⟩ := h
    use x
    constructor
    · apply hp
    · apply hq
  · intro h
    obtain ⟨x, ⟨hp, hq⟩⟩ := h
    constructor
    · use x
      apply hp
    · apply hq
