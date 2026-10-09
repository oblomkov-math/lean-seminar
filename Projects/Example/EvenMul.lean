/-
# Example project: an even integer times any integer is even

A filled-in copy of `Seminar/ProjectTemplate.lean`, for a problem easy enough
that the layout is the point, not the mathematics. Every section of the
template is here, in the same order, and `scripts/check.sh Projects/Example`
ends with PASS.

Your project goes in `Projects/<YourName>/<Problem>.lean`, with the namespace
`Projects.<YourName>`. This one is `Projects/Example/EvenMul.lean`, with the
namespace `Projects.Example`.
-/

import Mathlib

-- Seminar material, not a Mathlib contribution: the header linter's
-- copyright-block and docstring-placement rules do not apply here.
set_option linter.style.header false

namespace Projects.Example

/-! ## 0. The informal problem

> Show that the product of an even integer and any integer is even.

This problem stands in for a qualifying exam problem, which you would paste
here word for word, with the exam and the year.

What the informal statement leaves implicit, and what we decided:

* **Which numbers.** "Integer" means `ℤ`. The same proof works over `ℕ`, or
  over any ring, but the problem is about integers.
* **What "even" means.** In the course, `a` is even if `a = 2 * k` for some
  integer `k`. Mathlib's `Even a` says instead that `a = r + r` for some `r`.
  The two agree, and §2 checks this in Lean, so we may use Mathlib's `Even`.
* **"Any" integer.** The second factor gets no hypothesis: it may be odd,
  zero or negative. -/

/-! ## 1. Statement

The statement is a definition, `Statement`, rather than a `theorem`. A proof
can only use lemmas stated above it, and the lemmas come in §6, so the theorem
itself, `even_mul_any : Statement`, is proved at the end of §6. -/

/-- The problem in Lean: for all integers `a` and `b`, if `a` is even, then
`a * b` is even. -/
def Statement : Prop :=
  ∀ a b : ℤ, Even a → Even (a * b)

/-! ## 2. Prerequisite audit

Every mathematical object in §1, paired with its Mathlib declaration. -/

#check Int        -- the integers, `ℤ`
#check Int.mul    -- `a * b` on `ℤ`
#check @Even      -- `Even a`: there is an `r` with `a = r + r`

-- This is what `Even` means, by definition: the proof `Iff.rfl` says that the
-- two sides are the same statement.
example (a : ℤ) : Even a ↔ ∃ r, a = r + r := Iff.rfl

-- It agrees with the course's definition, `a = 2 * k`.
example (a : ℤ) : Even a ↔ ∃ k, a = 2 * k := even_iff_exists_two_mul

/- Missing from Mathlib: none. -/

/-! ## 3. Vacuity guard

An explicit object satisfying every hypothesis of §1. The only hypothesis is
`Even a`. Take `a = 2`; `b` has no hypothesis, so any integer will do, say
`b = 3`. -/

-- `2` is even, because `2 = 1 + 1`.
example : Even (2 : ℤ) := ⟨1, rfl⟩

/-! ## 4. Junk-value audit -/

/- Partial operations in the statement above: none.
   (`*` on `ℤ` is defined everywhere, and `Even` is a property, not an
   operation. Had we written "even" as `a % 2 = 0`, then `%` would need a line
   here: Lean sets `a % 0 = a`. We only divide by `2`, so that value never
   arises.) -/

/-! ## 5. Proof route

Three Mathlib declarations that appear in the finished proofs in §6. -/

#check @add_mul           -- `(a + b) * c = a * c + b * c`: the key step
#check @Even.mul_right    -- the problem itself, already in Mathlib
#check @even_iff_two_dvd  -- `Even a ↔ 2 ∣ a`, for a proof by divisibility

/-! ## 6. Proof

Top-down, as the template asks. The proof needs one fact about integers: if
`a = r + r`, then `a * b = r * b + r * b`. At the feasibility round this section
read

    lemma double_mul {a b r : ℤ} (hr : a = r + r) : a * b = r * b + r * b := by
      sorry

    theorem even_mul_any : Statement := by
      intro a b ha
      obtain ⟨r, hr⟩ := ha
      exact ⟨r * b, double_mul hr⟩

so the main theorem was already proved from the lemma. Since then, only the
`sorry` has been replaced. -/

/-- A double times anything is a double: if `a = r + r`, then
`a * b = r * b + r * b`. -/
lemma double_mul {a b r : ℤ} (hr : a = r + r) : a * b = r * b + r * b := by
  rw [hr, add_mul]

/-- **The main theorem.** An even integer times any integer is even. -/
theorem even_mul_any : Statement := by
  intro a b ha
  -- `ha : Even a` is a pair: a number `r`, and a proof that `a = r + r`.
  obtain ⟨r, hr⟩ := ha
  -- To prove `Even (a * b)`, give the number `r * b`, and a proof that
  -- `a * b = r * b + r * b`.
  exact ⟨r * b, double_mul hr⟩

/-! Two shorter proofs, for comparison. The first uses Mathlib's own lemma,
which `exact?` finds. The second goes through divisibility by `2`. -/

example : Statement := fun _ b ha => ha.mul_right b

example : Statement := by
  intro a b ha
  rw [even_iff_two_dvd] at ha ⊢
  exact ha.mul_right b

/-! ## 7. Axiom check

Show this for every main theorem in your presentation. -/

#print axioms even_mul_any

end Projects.Example
