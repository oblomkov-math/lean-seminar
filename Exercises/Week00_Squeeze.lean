import Mathlib

/-!
# Week 0: the squeeze theorem

Watch Alex Kontorovich's video "How Mathematicians can Get Started with Lean"
(32 minutes): https://www.youtube.com/watch?v=I2zaPoj3G50

Type along in this file as you watch. He defines what it means for a sequence
to converge, and then proves the squeeze theorem: if `a n ≤ b n ≤ c n` for every
`n`, and both `a` and `c` converge to `L`, then `b` converges to `L` too.

The definition and the theorem are already typed in below, so you can start with
the proof. The video begins by setting up Lean in the browser (steps 1–4 in the
video's description); you can skip that part and type here instead.

The video stops, at about 31:30, before the proof is finished. Finishing it is
the exercise. You are done when the `sorry` is gone and Lean shows no red or
yellow underline in this file.

## Hints

* Given `ε > 0`, take `N₁` from `a_to_L` and `N₂` from `c_to_L`, using the same
  `ε` for both.
* Use `max N₁ N₂` as the `N` for `b`.
* `rw [abs_lt]` splits `|x| < ε` into two inequalities, `-ε < x` and `x < ε`.
  It also works on a hypothesis `h`: `rw [abs_lt] at h`.
* `a_le_b n` is the fact `a n ≤ b n`, and `b_le_c n` is the fact `b n ≤ c n`.
* Once the facts you need are in the context, `linarith` finishes each of the
  two inequalities.
* To find a lemma, ask Lean: `apply?` and `exact?` search Mathlib. For example,
  they find `Nat.le_max_right`, which says `b ≤ max a b`.
-/

namespace Week00

def SeqConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε

theorem squeeze (a b c : ℕ → ℝ) (L : ℝ) (a_le_b : a ≤ b) (b_le_c : b ≤ c)
    (a_to_L : SeqConvergesTo a L) (c_to_L : SeqConvergesTo c L) :
    SeqConvergesTo b L := by
  sorry

end Week00
