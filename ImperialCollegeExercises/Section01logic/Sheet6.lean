/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro q
  exact Or.inr q

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl p =>
    intro pr _
    exact pr p
  | inr q =>
    intro _ qr
    exact qr q

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  obtain h | h := hPoQ
  · intro pr _
    exact pr h
  · intro _ qr
    exact qr h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h)
  · intro pr qr
    exact pr h
  · intro pr qr
    exact qr h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (p | q)
  · exact Or.inr p
  · exact Or.inl q

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro p
  sorry

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro p_r q_s p_or_q
  cases p_or_q with
  | inl p => exact Or.inl (p_r p)
  | inr q => exact Or.inr (q_s q)

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro p_q p_or_r
  cases p_or_r with
  | inl p => exact Or.inl (p_q p)
  | inr r => exact Or.inr r

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro p
  by_cases
  sorry
  sorry

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
