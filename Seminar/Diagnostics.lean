/-
# Seminar/Diagnostics.lean — statement fidelity toolkit

Lean checks `proof : statement`. It does NOT check that `statement` says what you
meant. Everything of mathematical consequence therefore lives in the statement,
and this file is the set of habits that keep statements honest.

Use this as the Week 6 lab. Items marked EXERCISE are deliberately incomplete:
the declaration names below were correct at time of writing but Mathlib renames
things, so confirming them against *your* pinned version is part of the point.
Use `exact?`, `#check`, Loogle, and LeanSearch.
-/

import Mathlib

-- Seminar material, not a Mathlib contribution: the header linter's
-- copyright-block and docstring-placement rules do not apply here.
set_option linter.style.header false

namespace Seminar.Diagnostics

/-! ## 1. Junk values

Lean's functions are total. Operations that are partial in mathematics are given
a default value at the undefined points. A statement that quantifies over those
points may be saying something other than what you intend. -/

-- Subtraction on ℕ truncates at zero.
example : (3 : ℕ) - 5 = 0 := by omega

-- Division by zero is zero. So is inversion of zero.
example (x : ℝ) : x / 0 = 0 := div_zero x
example : (0 : ℝ)⁻¹ = 0 := inv_zero

-- `Real.log` is zero off its natural domain.
example : Real.log 0 = 0 := Real.log_zero

-- The zero polynomial has `degree = ⊥` but `natDegree = 0`. Choosing the wrong
-- one silently changes the statement.
example : (0 : Polynomial ℚ).degree = ⊥ := Polynomial.degree_zero
example : (0 : Polynomial ℚ).natDegree = 0 := Polynomial.natDegree_zero

-- Empty sums are zero, empty products are one, and `⨆ i ∈ ∅` is `⊥`.
example (f : ℕ → ℝ) : ∑ i ∈ (∅ : Finset ℕ), f i = 0 := Finset.sum_empty

-- EXERCISE. Find the Mathlib name for: the square root of a nonpositive real is 0.
-- example (x : ℝ) (hx : x ≤ 0) : Real.sqrt x = 0 := sorry

/-! **Audit rule.** Before settling on any statement, list every occurrence of
`/`, `⁻¹`, `-` on `ℕ`, `Real.log`, `Real.sqrt`, `Real.rpow`, `degree`, `sInf`,
`sSup`, `Classical.choice`, and `Function.invFun`, and write one line saying why
the boundary behaviour is harmless for your intended meaning. -/
-- (documentation only)

/-! ## 2. Vacuity

A theorem whose hypotheses cannot be satisfied is valid Lean and worthless
mathematics. Lean will never warn you about this. -/

-- Perfectly well-typed. Perfectly useless.
theorem vacuous (n : ℕ) (h : n < 0) : 2 + 2 = 5 :=
  absurd h (Nat.not_lt_zero n)

/-- **Guard pattern.** For every theorem you state, exhibit an object satisfying
all of its hypotheses. If you cannot, either the problem is harder than you
think, or your statement is empty. -/
example : IsNoetherianRing ℤ := by infer_instance

-- EXERCISE. State a theorem about a non-Noetherian ring and then produce the
-- guard: an explicit ring witnessing that the hypothesis class is inhabited.

/-! ## 3. Axiom auditing

A finished proof should rest on at most `propext`, `Classical.choice`, and
`Quot.sound`. Anything else — above all `sorryAx` — means the proof is not a
proof. `lake build` only *warns* on `sorry`, so this check is not optional. -/

theorem two_add_two : (2 : ℕ) + 2 = 4 := by norm_num

#print axioms two_add_two
-- prints: 'two_add_two' depends on axioms: [propext]. That is one of the three
-- standard axioms, so the proof is complete.

#print axioms vacuous
-- also clean — which is exactly why axiom auditing does not substitute for §2.

/-! ## 4. Definitional traps

`rfl` succeeds up to definitional unfolding, which is not the same as the
equality a mathematician has in mind. Conversely, two Mathlib definitions that
are mathematically equivalent may not be *defeq*, and the bridge lemma between
them may be the hard part of your project.

Before relying on a Mathlib definition, unfold it and read it:
  `#print Ideal.height`
  `#print IsIntegrallyClosed`
  `unfold` / `simp only [Foo]` in a scratch goal

FATE records a state-of-the-art prover misreading `Ideal.height`, deriving a
contradiction, and concluding that the *problem statement* was flawed rather
than that its own reading of the library was wrong. You will do a version of
this. When Lean and your intuition disagree, the library is usually right and
your reading of it is usually wrong — check the definition before you blame
the problem. -/

/-! ## 5. Things that bypass the kernel

`native_decide` trusts the compiler, not just the Lean kernel, and enlarges the
trusted base substantially. `axiom` declarations do the same, explicitly.
Neither belongs in a finished seminar proof, and the completeness check flags
both (`scripts/check.sh`, or `scripts/lean-check.sh` in a kit-configured
project). -/

/-! ## 6. Performance

If elaboration is slow, measure before optimising.
  `set_option maxHeartbeats 1000000 in` (per-declaration, not file-wide)
  `set_option trace.profiler true in`
  `count_heartbeats in theorem foo ...`

A proof that needs a raised heartbeat limit usually wants `simp only [...]`
in place of bare `simp`, or an explicit `exact` in place of a search tactic. -/

end Seminar.Diagnostics
