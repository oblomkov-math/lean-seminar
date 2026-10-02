import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

-- five proofs of the same theorem
theorem thm1 (a b c d e : ℝ) (h1: a < b) (h2: b ≤ c) (h3: c < d) (h4: d ≤ e) : a < e :=
  lt_trans (lt_of_lt_of_le h1 h2) (lt_of_lt_of_le h3 h4)

theorem thm2 (a b c d e : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) (h4 : d ≤ e) : a < e := by
  apply lt_trans
  . apply lt_of_lt_of_le
    . exact h1
    . exact h2
  . apply lt_of_lt_of_le
    . exact h3
    . exact h4

theorem thm3 (a b c d e : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) (h4 : d ≤ e) : a < e :=
  calc
    a < b := h1
    _ ≤ c := h2
    _ < d := h3
    _ ≤ e := h4

theorem thm4 (a b c d e : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) (h4 : d ≤ e) : a < e := by
  linarith

theorem thm5 (a b c d e : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) (h4 : d ≤ e) : a < e := by
  grind
