/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro t
  trivial

example : False → ¬True := by
  intro f
  trivial

example : ¬False → True := by
  intro nf
  trivial

example : True → ¬False := by
  intro t
  trivial

example : False → ¬P := by
  intro f
  trivial

example : P → ¬P → False := by
  intro p np
  trivial

example : P → ¬¬P := by
  intro p
  unfold Not
  intro p'
  exact p' p

example : (P → Q) → ¬Q → ¬P := by
  intro pq neg_q
  unfold Not
  intro p
  have q := pq p
  trivial

example : ¬¬False → False := by
  intro f
  trivial

example : ¬¬P → P := by
  intro nn_p
  by_contra
  unfold Not at this
  unfold Not at nn_p
  exact nn_p this

example : (¬Q → ¬P) → P → Q := by
  intro nq_np p
  by_contra
  have n_p := nq_np this
  trivial
