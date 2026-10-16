/-
# Example project: Lagrange's theorem

A filled-in copy of `Seminar/ProjectTemplate.lean`, for a theorem with a short
proof: if `H` is a subgroup of a finite group `G`, then `|G| = |H| · [G : H]`.
In particular, `|H|` divides `|G|`.

The proof is the textbook one. The left cosets of `H` cut `G` into pieces, and
each piece has `|H|` elements.

Mathlib already contains Lagrange's theorem, as `Subgroup.card_mul_index`. The
proof below does not use it. It defines cosets from scratch, and apart from the
axioms of groups and subgroups, it takes from Mathlib only general facts about
counting, listed in §5. §7 compares the result with Mathlib's.

How to read this file: open the InfoView (Cmd+Shift+Enter) and click on a line
inside a proof. The InfoView shows what is known at that point, above the
symbol `⊢`, and what remains to be proved, below it.
-/

import Mathlib

-- Seminar material, not a Mathlib contribution: the header linter's
-- copyright-block and docstring-placement rules do not apply here.
set_option linter.style.header false

namespace Projects.Example

/-! ## 0. The informal problem

> **Lagrange's theorem.** Let `G` be a finite group and `H` a subgroup of `G`.
> Then `|G| = |H| · [G : H]`, where `[G : H]` is the number of left cosets of
> `H`. In particular, `|H|` divides `|G|`.

This stands in for a qualifying exam problem. The statement is the standard
textbook one.

What the informal statement leaves implicit, and what we decided:

* **Cosets.** The left coset of `g` is the set `gH = {gh | h ∈ H}`. Different
  elements can have the same coset, and `[G : H]` counts the distinct cosets.
* **Counting.** `[G : H]` is the size of a set whose elements are themselves
  sets: the cosets. -/

/-! ## 1. Statement

As in `EvenMul.lean`, the theorem is stated as a definition, `Lagrange`, and
proved at the end of §6, because a proof can only use lemmas stated above it.

First, the vocabulary that the statement uses. -/

/-- The **left coset** `gH = {g * h | h ∈ H}`.

`{x | …}` is the set of all `x` such that `…`, and `∃ h ∈ H, g * h = x` says
that `x = g * h` for some `h` in `H`. -/
def coset {G : Type*} [Group G] (g : G) (H : Subgroup G) : Set G :=
  {x | ∃ h ∈ H, g * h = x}

/-- The set of all left cosets of `H`: the sets `C` with `C = gH` for some `g`. -/
def cosets {G : Type*} [Group G] (H : Subgroup G) : Set (Set G) :=
  {C | ∃ g : G, C = coset g H}

/-- The **index** `[G : H]`: the number of left cosets of `H`.

`Nat.card S` is the number of elements of `S`. (`noncomputable` because Lean
cannot evaluate `Nat.card`; this changes nothing in proofs.) -/
noncomputable def numCosets {G : Type*} [Group G] (H : Subgroup G) : ℕ :=
  Nat.card (cosets H)

/-- **Lagrange's theorem.** If `G` is finite, then `|G| = |H| · [G : H]` for every
subgroup `H` of `G`. -/
def Lagrange (G : Type*) [Group G] : Prop :=
  Finite G → ∀ H : Subgroup G, Nat.card G = Nat.card H * numCosets H

/-! ## 2. Prerequisite audit

Every mathematical object in §1, paired with its Mathlib declaration. -/

#check @Group      -- a group
#check @Finite     -- "is finite"
#check @Subgroup   -- the subgroups of a group
#check @Nat.card   -- the number of elements, `|G|`

open Pointwise in
/-- **Our cosets are Mathlib's.** Mathlib writes the left coset `gH` as `g • H`,
a notation that `open Pointwise` switches on. The two definitions say the same
thing word for word, so the proof is `rfl`: "true by definition". -/
example {G : Type*} [Group G] (g : G) (H : Subgroup G) : coset g H = g • (H : Set G) := rfl

/- Missing from Mathlib: none. (Mathlib also has the index, as `H.index`; §7
   checks that it agrees with `numCosets H`.) -/

/-! ## 3. Vacuity guard

An explicit object satisfying every hypothesis of §1, that is, a finite group
and a subgroup: the symmetric group `S₃`, which Mathlib writes
`Equiv.Perm (Fin 3)` (the permutations of `{0, 1, 2}`), and its alternating
group `A₃`. `|S₃| = 6` and `|A₃| = 3`, so Lagrange's theorem predicts
`[S₃ : A₃] = 2`. §6 ends by confirming this. -/

example : Finite (Equiv.Perm (Fin 3)) := inferInstance

-- `simp` leaves the goal `Fintype.card (Equiv.Perm (Fin 3)) = 6`, and `rfl`
-- makes Lean compute the left side.
theorem card_S₃ : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  simp; rfl

-- `decide` lists the six permutations and counts the even ones.
theorem card_A₃ : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card]; decide

/-! ## 4. Junk-value audit -/

/- Partial operations in the statement above:

   * `Nat.card`: Lean sets `Nat.card S = 0` when `S` is infinite. For an
     infinite group, the formula would compare such junk values, so the
     statement assumes `Finite G`. Then `G`, `H` and the set of cosets are all
     finite, and `Nat.card` is the honest count.

   No division or subtraction appears. -/

/-! ## 5. Proof route

The proof in §6, in four steps:

1. `x ∈ gH` exactly when `g⁻¹ x ∈ H`. In particular, `g ∈ gH`.
2. If `x ∈ gH`, then `xH = gH`: two cosets with an element in common are equal.
3. Each coset `gH` has `|H|` elements, because `h ↦ gh` is injective.
4. Sort the elements of `G` by their coset. By steps 1 and 2, the elements
   whose coset is `gH` are the elements of `gH`, and by step 3 there are `|H|`
   of them. So `|G|` is a sum of `[G : H]` terms, each equal to `|H|`.

Besides the axioms of groups and subgroups, the proof uses these facts from Mathlib: -/

-- An injective map does not change the number of elements.
#check @Nat.card_image_of_injective
-- Sorting a set into classes: the set corresponds to the pairs (class, element of it).
#check @Equiv.sigmaFiberEquiv
-- ... so its size is the sum of the sizes of the classes.
#check @Nat.card_sigma
-- A sum of equal terms: `∑ x ∈ s, m = |s| · m`.
#check @Finset.sum_const_nat

/-! ## 6. Proof -/

section Proofs

-- From here to `end Proofs`, `G` is a group: every theorem below takes it as an argument.
variable {G : Type*} [Group G]

/-! ### 6.1 Membership in a coset -/

/-- `x ∈ gH` exactly when `g⁻¹ x ∈ H`.

Proof. If `x = gh` with `h ∈ H`, then `g⁻¹ x = h ∈ H`. Conversely, if
`g⁻¹ x ∈ H`, then `x = g (g⁻¹ x)` has the required form, with `h = g⁻¹ x`. -/
theorem mem_coset {g x : G} {H : Subgroup G} : x ∈ coset g H ↔ g⁻¹ * x ∈ H := by
  constructor
  · -- Suppose `x = g * h` with `h ∈ H`.
    rintro ⟨h, hh, rfl⟩
    -- The goal is `g⁻¹ * (g * h) ∈ H`, and `g⁻¹ * (g * h) = h`.
    rw [inv_mul_cancel_left]
    exact hh
  · -- Suppose `g⁻¹ * x ∈ H`. Take `h = g⁻¹ * x`; then `g * h = x`.
    intro hx
    exact ⟨g⁻¹ * x, hx, mul_inv_cancel_left g x⟩

/-- Every element lies in its own coset: `g ∈ gH`, because `g⁻¹ g = 1 ∈ H`. -/
theorem mem_coset_self (g : G) (H : Subgroup G) : g ∈ coset g H := by
  rw [mem_coset, inv_mul_cancel]
  exact H.one_mem

/-! ### 6.2 Cosets with an element in common are equal -/

/-- If `x ∈ gH`, then `xH = gH`.

Proof. We have `g⁻¹ x ∈ H`. By 6.1, we must show that `x⁻¹ y ∈ H` exactly when
`g⁻¹ y ∈ H`, for every `y ∈ G`.

Lean: `ext y` reduces an equality of sets to "the same elements `y`". The
`group` tactic proves equations that hold in every group. -/
theorem coset_eq_of_mem {g x : G} {H : Subgroup G} (hx : x ∈ coset g H) :
    coset x H = coset g H := by
  rw [mem_coset] at hx
  ext y
  rw [mem_coset, mem_coset]
  constructor
  · -- If `x⁻¹ y ∈ H`, then `g⁻¹ y = (g⁻¹ x)(x⁻¹ y)` is a product of two elements of `H`.
    intro hy
    have e : g⁻¹ * y = (g⁻¹ * x) * (x⁻¹ * y) := by group
    rw [e]
    exact H.mul_mem hx hy
  · -- If `g⁻¹ y ∈ H`, then `x⁻¹ y = (g⁻¹ x)⁻¹ (g⁻¹ y)` is one too.
    intro hy
    have e : x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group
    rw [e]
    exact H.mul_mem (H.inv_mem hx) hy

/-- `xH = gH` exactly when `x ∈ gH`. One direction is the lemma above. For the
other, `x ∈ xH` by 6.1, so if `xH = gH`, then `x ∈ gH`. -/
theorem coset_eq_iff {g x : G} {H : Subgroup G} : coset x H = coset g H ↔ x ∈ coset g H := by
  constructor
  · intro h
    rw [← h]
    exact mem_coset_self x H
  · exact coset_eq_of_mem

/-! ### 6.3 Every coset has `|H|` elements -/

/-- `|gH| = |H|`.

Proof. `gH` is the image of `H` under the map `h ↦ g h`, which is injective:
`g h = g h'` implies `h = h'`. An injective map does not change the number of
elements.

Lean: `mul_right_injective g` says that `h ↦ g * h` is injective. Mathlib
defines the image of a set exactly as we defined `coset` in §1, so
`Nat.card_image_of_injective` applies to `coset g H` as it stands. -/
theorem card_coset (g : G) (H : Subgroup G) : Nat.card (coset g H) = Nat.card H :=
  Nat.card_image_of_injective (mul_right_injective g) H

/-! ### 6.4 Counting -/

/-- **Lagrange's formula** `|G| = |H| · [G : H]`.

Proof. Send each `x ∈ G` to its coset `xH`. Sorting the elements of `G` by their
coset gives `|G| = ∑_C #{x : xH = C}`, a sum with one term for each coset `C`.
For `C = gH`, the elements `x` with `xH = gH` are exactly the elements of `gH`
(6.2), and there are `|H|` of them (6.3). So the sum has `[G : H]` terms, each
equal to `|H|`.

Lean: `f x` is the coset `xH`, seen as an element of the set of all cosets.
`{x // f x = C}` is the set of `x` with `f x = C`, and `∑ C : cosets H, …` is
the sum over all cosets `C`. -/
theorem card_eq_card_mul_numCosets [Finite G] (H : Subgroup G) :
    Nat.card G = Nat.card H * numCosets H := by
  -- Lean needs a finite list of the cosets to sum over them; this line provides one.
  have := Fintype.ofFinite (cosets H)
  let f : G → cosets H := fun x => ⟨coset x H, x, rfl⟩
  -- Step 1. Sort the elements of `G` by their coset.
  have step1 : Nat.card G = ∑ C : cosets H, Nat.card {x // f x = C} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  -- Step 2. Each term is `|H|`.
  have step2 : ∀ C : cosets H, Nat.card {x // f x = C} = Nat.card H := by
    -- Let `C` be a coset, `C = gH`. By 6.3, it is enough to compare with `|gH|`.
    rintro ⟨_, g, rfl⟩
    rw [← card_coset g H]
    -- Two sets of elements of `G` have the same size if the conditions defining
    -- them are equivalent.
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    -- `f x = gH` is an equation between cosets; `Subtype.ext_iff` turns it into
    -- an equation between sets, which `show` displays in plain form.
    rw [Subtype.ext_iff]
    show coset x H = coset g H ↔ x ∈ coset g H
    exact coset_eq_iff
  -- Step 3. A sum of `[G : H]` terms, each equal to `|H|`.
  rw [step1, Finset.sum_const_nat fun C _ => step2 C]
  -- The goal is now `Finset.univ.card * |H| = |H| * numCosets H`. Lean has several
  -- ways to count a finite set; the last line converts `Finset.univ.card`, the
  -- number of cosets as Lean counted them in the sum, to `numCosets H`.
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, numCosets, mul_comm]

/-- **Corollary.** `|H|` divides `|G|`.

Lean: `a ∣ b` means that `b = a * c` for some `c`. Here `c = [G : H]`, and the
equation `|G| = |H| · [G : H]` is the formula above. -/
theorem card_subgroup_dvd [Finite G] (H : Subgroup G) : Nat.card H ∣ Nat.card G :=
  ⟨numCosets H, card_eq_card_mul_numCosets H⟩

end Proofs

/-! ### 6.5 The statement of §1

`Lagrange G` assumes `Finite G` as an ordinary hypothesis. The formula above
takes it in square brackets, as an *instance*, which Lean supplies by itself. A
hypothesis `Finite G` already is one, so nothing needs converting. -/

theorem lagrange (G : Type*) [Group G] : Lagrange G := fun _ H =>
  card_eq_card_mul_numCosets H

/-! ### 6.6 Back to the example of §3

`[S₃ : A₃] = 2`, as predicted: Lagrange's formula reads `6 = 3 · [S₃ : A₃]`. -/

example : numCosets (alternatingGroup (Fin 3)) = 2 := by
  have h := card_eq_card_mul_numCosets (alternatingGroup (Fin 3))
  rw [card_S₃, card_A₃] at h
  -- Now `h : 6 = 3 * numCosets (alternatingGroup (Fin 3))`, and `omega` solves for it.
  omega

/-! ## 7. Axiom check

Show this for every main theorem in your presentation. -/

#print axioms lagrange

/-! The line reports `[propext, Classical.choice, Quot.sound]`: the three
standard axioms, and no `sorryAx`.

**A cross-check with Mathlib.** Mathlib counts cosets in its own way, through
the quotient `G ⧸ H`, and calls the count `H.index`. Mathlib's Lagrange formula
and ours give the same number. -/

example {G : Type*} [Group G] [Finite G] (H : Subgroup G) : numCosets H = H.index := by
  have ours := card_eq_card_mul_numCosets H   -- `|G| = |H| · numCosets H`
  have mathlib := H.card_mul_index            -- `|H| · H.index = |G|`
  rw [ours] at mathlib
  -- `mathlib : |H| · H.index = |H| · numCosets H`. Cancel `|H|`, which is positive.
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos mathlib).symm

end Projects.Example
