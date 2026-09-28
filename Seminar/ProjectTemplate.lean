/-
# Project template — feasibility check and project, weeks 11–14

Copy this file to `Projects/<YourName>/<Problem>.lean`, for example
`Projects/AdaLovelace/Sylow56.lean`, and fill in every section. In your copy,
rename the namespace `Seminar.Projects.Template` to `Projects.<YourName>`: the
`namespace` line below and the `end` line at the bottom.

For the week-11 feasibility round, aim to have §0–§5 filled in and compiling: a
statement that does not typecheck is not yet a statement.

The five triage items exist because the failure they prevent is silent: a
formalization can compile, contain no `sorry`, and still state nothing.
-/

import Mathlib

-- Seminar material, not a Mathlib contribution: the header linter's
-- copyright-block and docstring-placement rules do not apply here.
set_option linter.style.header false

namespace Seminar.Projects.Template

/-! ## 0. The informal problem

Paste the qualifying exam problem verbatim, including the year and the exam.
Note anything the informal statement leaves implicit: standing assumptions from
the course, conventions about whether rings are commutative or have a unit,
whether "module" means left or right, and so on. Every implicit convention has
to become an explicit hypothesis, and deciding which ones is the mathematics. -/

/-! ## 1. Statement

Must typecheck. `sorry` in the proof is expected at the feasibility round;
`sorry` in the statement is not a statement. -/

-- Replace with your problem.
theorem my_problem {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : (⊥ : Ideal R) ≤ I := by
  exact bot_le

/-! ## 2. Prerequisite audit

Every mathematical object in §1, paired with its Mathlib declaration. Use
`#check` so the audit is machine-verified rather than asserted.

Objects with no Mathlib counterpart go in the table below with an estimate of
the supporting API each will need. For calibration: 38% of FATE-X problems
required new definitions, averaging 2.4 per problem, and those were written by
Mathlib contributors. Two new definitions is an ambitious semester. -/

#check @IsNoetherianRing
#check @Ideal
#check @bot_le

/- Missing from Mathlib (fill in, or write "none"):
   | object | why absent | `def` + lemmas needed |
   |--------|------------|------------------------|
   |        |            |                        |
-/

/-! ## 3. Vacuity guard

An explicit object satisfying every hypothesis of §1. Not a proof that such an
object could exist — an actual witness. -/

example : IsNoetherianRing ℤ := by infer_instance

/-! ## 4. Junk-value audit

List each partial operation appearing in §1 and justify the boundary behaviour
in one line. If §1 contains none, say so explicitly — that is a real finding,
not an empty section. -/

/- Partial operations in the statement above: none.
   (`Ideal.le` is total; no division, subtraction on ℕ, or logarithms appear.) -/

/-! ## 5. Proof route

At least three Mathlib declarations you expect to appear in the finished proof.
`#check` each one. If you cannot name three, you have not yet located the
argument inside the library, and the proof cost is unknown rather than large. -/

#check @IsNoetherianRing.isNilpotent_nilradical
#check @Ideal.IsPrime
#check @Ideal.radical

/-! ## 6. Proof

Develop top-down. State the lemmas you need, `sorry` them, prove the main
theorem from them, then discharge the lemmas one at a time. This keeps the
skeleton honest and makes progress measurable.

A `sorry`-ed decomposition is a restatement, not progress. Aim to have at least
one non-trivial lemma fully proved by the feasibility round. -/

/-! ## 7. Axiom check

Show this for every main theorem in your presentation. -/

#print axioms my_problem

end Seminar.Projects.Template
