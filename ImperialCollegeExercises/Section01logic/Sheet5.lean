/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro ⟨p, q⟩
  exact ⟨q, p⟩

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;> intro thing <;> exact ⟨thing.2, thing.1⟩

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro PiffQ QiffP
  constructor
  exact QiffP.1 ∘ PiffQ.1
  exact PiffQ.2 ∘ QiffP.2

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro p
  rw [and_assoc] at p
  exact p
  intro p
  rw [← and_assoc] at p
  exact p

example : P ↔ P ∧ True := by
  constructor
  intro p
  exact ⟨p, True.intro⟩
  intro ⟨p, _⟩
  exact p

example : False ↔ P ∧ False := by
  constructor
  intro f
  trivial
  intro ⟨_, h⟩
  exact h

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  -- oh my god this is a slog
  grind

example : ¬(P ↔ ¬P) := by
  sorry
