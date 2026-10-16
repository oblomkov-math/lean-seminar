/-
# Example project: Sylow's theorems

A second filled-in copy of `Seminar/ProjectTemplate.lean`, this time with a
serious proof. We prove all three Sylow theorems: existence, conjugacy, and
the count of Sylow subgroups. The proofs are the classical ones, by group
actions, found in most algebra textbooks.

What comes from Mathlib, and what is proved here:

* Mathlib supplies general group theory: Lagrange's theorem, the
  orbit–stabilizer theorem, quotient groups, Cauchy's theorem, and one
  counting lemma about `p`-groups. §5 lists them.
* Mathlib also contains the Sylow theorems themselves, in
  `Mathlib/GroupTheory/Sylow.lean`. The proofs below use nothing from that
  file. §2 uses it once, to check that our definition of a Sylow subgroup
  agrees with Mathlib's, and §7 checks mechanically that the proofs never
  touch it.

How to read this file: open it in VS Code with the InfoView showing
(Cmd+Shift+Enter), and click inside a proof to see what remains to be proved
at that point. Most explanations come twice: first the mathematics, then the
Lean.
-/

import Mathlib

-- Seminar material, not a Mathlib contribution: the header linter's
-- copyright-block and docstring-placement rules do not apply here.
set_option linter.style.header false

namespace Projects.Example

/-! ## 0. The informal problem

> **Sylow's theorems.** Let `G` be a finite group and `p` a prime, and write
> `|G| = p^n · m` with `p ∤ m`. A *Sylow `p`-subgroup* of `G` is a subgroup of
> order `p^n`. Then:
>
> 1. `G` has a Sylow `p`-subgroup.
> 2. Any two Sylow `p`-subgroups of `G` are conjugate.
> 3. The number `n_p` of Sylow `p`-subgroups satisfies `n_p ≡ 1 (mod p)` and
>    `n_p ∣ m`.

This stands in for a qualifying exam problem. The statement is the standard
textbook one.

What the informal statement leaves implicit, and what we decided:

* **The exponent `n`.** "`|G| = p^n · m` with `p ∤ m`" defines `n` as the
  exponent of `p` in `|G|`. Lean has a name for this number:
  `(Nat.card G).factorization p`. Then `m = |G| / p^n`. If `p ∤ |G|`, then
  `n = 0` and the Sylow `p`-subgroup is the trivial subgroup; the theorems
  still hold.
* **"Sylow subgroup".** We use the textbook definition, by order. Mathlib
  defines a Sylow subgroup instead as a maximal `p`-subgroup. For finite groups
  the two agree, and §2 checks this in Lean.
* **"Conjugate".** `Q` is conjugate to `P` if `Q = g P g⁻¹` for some `g ∈ G`.
* **Counting.** `n_p` counts subgroups, not elements: it is the size of a set
  whose elements are subgroups. -/

/-! ## 1. Statement

As in `EvenMul.lean`, the theorems are stated as definitions, `SylowI`,
`SylowII` and `SylowIII`, and proved at the end of §6, because a proof can
only use lemmas stated above it.

First, the vocabulary that the statements use. -/

/-- A **Sylow `p`-subgroup** of `G`, by the textbook definition: a subgroup of
order `p ^ n`, where `p ^ n` is the largest power of `p` dividing `|G|`.

`Nat.card P` is the number of elements of `P`. `(Nat.card G).factorization p`
is the exponent of `p` in `|G|`; for example, `(12).factorization 2 = 2`. -/
def IsSylowSubgroup {G : Type*} [Group G] (p : ℕ) (P : Subgroup G) : Prop :=
  Nat.card P = p ^ (Nat.card G).factorization p

/-- The **conjugate subgroup** `g P g⁻¹`: the image of `P` under the
automorphism `x ↦ g * x * g⁻¹` of `G`, which Mathlib calls `MulAut.conj g`. -/
def conjugate {G : Type*} [Group G] (g : G) (P : Subgroup G) : Subgroup G :=
  P.map (MulAut.conj g).toMonoidHom

/-- The Sylow `p`-subgroups of `G`, collected into a type. An element is a pair
`⟨P, h⟩` of a subgroup `P` and a proof `h` that `P` is a Sylow `p`-subgroup. -/
abbrev SylowSet (p : ℕ) (G : Type*) [Group G] : Type _ :=
  {P : Subgroup G // IsSylowSubgroup p P}

/-- `n_p`, the number of Sylow `p`-subgroups of `G`. (`noncomputable` because
`Nat.card` is a count that Lean cannot evaluate; this changes nothing in
proofs.) -/
noncomputable def numSylow (p : ℕ) (G : Type*) [Group G] : ℕ :=
  Nat.card (SylowSet p G)

/-- **Sylow I.** A finite group has a Sylow `p`-subgroup, for every prime `p`. -/
def SylowI (p : ℕ) (G : Type*) [Group G] : Prop :=
  Finite G → p.Prime → ∃ P : Subgroup G, IsSylowSubgroup p P

/-- **Sylow II.** In a finite group, any two Sylow `p`-subgroups are
conjugate. -/
def SylowII (p : ℕ) (G : Type*) [Group G] : Prop :=
  Finite G → p.Prime → ∀ P Q : Subgroup G, IsSylowSubgroup p P → IsSylowSubgroup p Q →
    ∃ g : G, Q = conjugate g P

/-- **Sylow III.** In a finite group, `n_p ≡ 1 (mod p)`, and `n_p` divides
`m = |G| / p ^ n`. -/
def SylowIII (p : ℕ) (G : Type*) [Group G] : Prop :=
  Finite G → p.Prime →
    numSylow p G ≡ 1 [MOD p] ∧ numSylow p G ∣ Nat.card G / p ^ (Nat.card G).factorization p

/-! ## 2. Prerequisite audit

Every mathematical object in §1, paired with its Mathlib declaration. -/

#check @Group              -- a group
#check @Finite             -- "is finite"
#check @Nat.Prime          -- "is prime"
#check @Subgroup           -- the subgroups of a group
#check @Nat.card           -- the number of elements, `|G|`
#check @Nat.factorization  -- `n.factorization p` is the exponent of `p` in `n`
#check @MulAut.conj        -- `MulAut.conj g` is the automorphism `x ↦ g * x * g⁻¹`
#check @Subgroup.map       -- the image of a subgroup under a homomorphism
#check @Nat.ModEq          -- `a ≡ b [MOD n]`

/-- **Our definition agrees with Mathlib's.** Mathlib's type `Sylow p G`
consists of the maximal `p`-subgroups of `G`. Mathlib proves that these are
exactly the subgroups of order `p ^ n` (`Sylow.ofCard` in one direction,
`Sylow.card_eq_multiplicity` in the other), and that gives this check. It is
the only use of Mathlib's Sylow theory in this file. -/
example {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Subgroup G) :
    IsSylowSubgroup p P ↔ ∃ S : Sylow p G, (S : Subgroup G) = P :=
  ⟨fun h => ⟨Sylow.ofCard P h, Sylow.coe_ofCard P h⟩,
    fun ⟨S, hS⟩ => hS ▸ S.card_eq_multiplicity⟩

/- Missing from Mathlib: none. -/

/-! ## 3. Vacuity guard

An explicit object satisfying every hypothesis of §1, that is, a finite group
and a prime: the symmetric group `S₃`, which Mathlib writes
`Equiv.Perm (Fin 3)` (the permutations of `{0, 1, 2}`), and `p = 3`.

As a further check that `IsSylowSubgroup` means what we want, we confirm the
prediction of Sylow I by hand. `|S₃| = 6 = 3 · 2`, so a Sylow 3-subgroup has
order `3`, and the alternating group `A₃` is one. -/

example : Finite (Equiv.Perm (Fin 3)) ∧ Nat.Prime 3 := ⟨inferInstance, Nat.prime_three⟩

example : IsSylowSubgroup 3 (alternatingGroup (Fin 3)) := by
  -- `simp` leaves the goal `Fintype.card (Equiv.Perm (Fin 3)) = 6`, and `rfl`
  -- makes Lean compute the left side.
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 2 * 3 := by simp; rfl
  -- `decide` lists the six permutations and counts the even ones.
  have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  -- The exponent of `3` in `2 * 3` is (exponent in `2`) + (exponent in `3`) = 0 + 1.
  rw [IsSylowSubgroup, h6, h3, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_two.factorization, Nat.prime_three.factorization]

/-! ## 4. Junk-value audit -/

/- Partial operations in the statement above:

   * `Nat.card`: Lean sets `Nat.card X = 0` when `X` is infinite. For an
     infinite group, `IsSylowSubgroup p P` would then say `Nat.card P = 1`
     (because `(0).factorization p = 0`), and Sylow I would hold trivially,
     with `P = ⊥`. So every statement assumes `Finite G`, and then `Nat.card`
     is the honest count.
   * `factorization`: for `p` not prime, `n.factorization p = 0`. Every
     statement assumes that `p` is prime.
   * `/` in `Nat.card G / p ^ n`: division on `ℕ` rounds down, but `p ^ n`
     divides `|G|` (`Nat.ordProj_dvd`), so here the division is exact and the
     result is `m`.
   * `numSylow`: `Nat.card` of the set of Sylow subgroups. A finite group has
     finitely many subgroups, so this is the honest count, never the junk value
     of an infinite set. -/

/-! ## 5. Proof route

The general facts from Mathlib that carry the proofs in §6. -/

-- Lagrange's theorem: `|H| · [G : H] = |G|`.
#check @Subgroup.card_mul_index
-- The counting lemma: if a `p`-group acts on a finite set `X`, then
-- `|X| ≡ |fixed points| (mod p)`.
#check @IsPGroup.card_modEq_card_fixedPoints
-- Cauchy's theorem: if `p ∣ |G|`, then `G` has an element of order `p`.
#check @exists_prime_orderOf_dvd_card'
-- Orbit–stabilizer: the index of the stabilizer of `x` is the size of the orbit of `x`.
#check @MulAction.index_stabilizer

/-! ## 6. Proof

The plan, in the order of the subsections:

* **6.1 Conjugate subgroups.** Basic facts about `g P g⁻¹`.
* **6.2 The counting tool.** A `p`-group acting on a set whose size is not
  divisible by `p` has a fixed point.
* **6.3 Sylow I.** Grow `p`-subgroups one factor of `p` at a time: subgroups
  of order `p, p², …, p^n` all exist.
* **6.4 Sylow II.** Every `p`-subgroup lies in a conjugate of a given Sylow
  subgroup. For a Sylow subgroup, lying in means equal.
* **6.5 Sylow III.** `G` acts on its Sylow subgroups by conjugation. A Sylow
  subgroup `P` has exactly one fixed point, `P` itself, which gives
  `n_p ≡ 1 (mod p)`. The action has a single orbit (Sylow II), which gives
  `n_p = [G : N(P)]`, a divisor of `m`.
* **6.6 The statements of §1**, assembled from the pieces.

`N(P)` is the normalizer of `P`, the set of `g` with `g P g⁻¹ = P`; Mathlib
writes it `Subgroup.normalizer (P : Set G)`. -/

section Proofs

-- From here to `end Proofs`, `G` is a group: every theorem below takes it as an argument.
variable {G : Type*} [Group G]

/-! ### 6.1 Conjugate subgroups -/

/-- `x ∈ g P g⁻¹` exactly when `g⁻¹ x g ∈ P`.

Lean: `Subgroup.mem_map_equiv` says that `x` lies in the image of `P` under an
isomorphism `f` exactly when `f⁻¹ x ∈ P`, and `MulAut.conj_symm_apply`
computes the inverse of conjugation by `g`: it is `x ↦ g⁻¹ * x * g`. -/
theorem mem_conjugate {g x : G} {P : Subgroup G} :
    x ∈ conjugate g P ↔ g⁻¹ * x * g ∈ P := by
  rw [conjugate, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- `g P g⁻¹` has as many elements as `P`, because conjugation is injective. -/
theorem card_conjugate (g : G) (P : Subgroup G) :
    Nat.card (conjugate g P) = Nat.card P :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- Conjugating by `1` changes nothing.

Lean: `ext x` reduces an equality of subgroups to "they have the same
elements", and `simp` simplifies `1⁻¹ * x * 1` to `x`. -/
theorem conjugate_one (P : Subgroup G) : conjugate 1 P = P := by
  ext x
  simp [mem_conjugate]

/-- Conjugating by `g * h` is conjugating by `h`, then by `g`:
`(gh) P (gh)⁻¹ = g (h P h⁻¹) g⁻¹`. -/
theorem conjugate_mul (g h : G) (P : Subgroup G) :
    conjugate (g * h) P = conjugate g (conjugate h P) := by
  ext x
  simp [mem_conjugate, mul_assoc]

/-- Conjugating a subgroup by one of its own elements changes nothing: if
`g ∈ P`, then `g P g⁻¹ = P`. -/
theorem conjugate_eq_self {g : G} {P : Subgroup G} (hg : g ∈ P) : conjugate g P = P := by
  ext x
  rw [mem_conjugate]
  constructor
  · -- If `g⁻¹ x g ∈ P`, then `x = g (g⁻¹ x g) g⁻¹ ∈ P`.
    intro h
    simpa [mul_assoc] using P.mul_mem (P.mul_mem hg h) (P.inv_mem hg)
  · -- If `x ∈ P`, then `g⁻¹ x g ∈ P`, as a product of three elements of `P`.
    intro h
    exact P.mul_mem (P.mul_mem (P.inv_mem hg) h) hg

/-! ### 6.2 The counting tool

All three theorems rest on one counting lemma. Let a `p`-group `H` act on a
finite set `X`. By orbit–stabilizer, each orbit has `[H : stabilizer]`
elements, a divisor of `|H|`, hence a power of `p`. An orbit with one element
is a fixed point, and every other orbit has a size divisible by `p`. Since `X`
is the disjoint union of its orbits,

    |X| ≡ |fixed points|  (mod p).

Mathlib proves this as `IsPGroup.card_modEq_card_fixedPoints`. We use it in
the following form. -/

/-- If a `p`-group `H` acts on a finite set `X` and `p ∤ |X|`, then the action
has a fixed point.

Proof: `|X| ≡ |fixed points| (mod p)`, so `p` does not divide the number of
fixed points either. In particular, that number is not `0`.

Lean: `IsPGroup p H` says that every element of `H` has order a power of `p`.
`Nat.ModEq.dvd_iff` turns the congruence into `p ∣ |X| ↔ p ∣ |fixed points|`.
`rcases isEmpty_or_nonempty` then splits into two cases. Either there are no
fixed points, so their number is `0`, which `p` divides, and `simp` finds the
contradiction; or there is a fixed point `a`. -/
theorem exists_fixedPoint {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] (hH : IsPGroup p H)
    (X : Type*) [MulAction H X] [Finite X] (hX : ¬ p ∣ Nat.card X) :
    ∃ a : X, ∀ h : H, h • a = a := by
  have hfix : ¬ p ∣ Nat.card (MulAction.fixedPoints H X) := by
    rwa [← (hH.card_modEq_card_fixedPoints X).dvd_iff dvd_rfl]
  rcases isEmpty_or_nonempty (MulAction.fixedPoints H X) with h | ⟨⟨a, ha⟩⟩
  · simp at hfix
  · exact ⟨a, MulAction.mem_fixedPoints.1 ha⟩

/-! ### 6.3 Sylow I: existence

The idea is to build subgroups of order `p, p², …, p^n` one at a time.
Suppose `H` has order `p ^ k`, and `p ^ (k+1)` still divides `|G|`.

1. `p` divides `[G : H] = |G| / p ^ k`.
2. `H` acts on the cosets `G ⧸ H` by left multiplication. `H` is a `p`-group,
   so by the counting lemma the number of fixed cosets is
   `≡ [G : H] ≡ 0 (mod p)`.
3. The coset `xH` is fixed exactly when `x` normalizes `H`. So the elements of
   `G` lying in fixed cosets are the elements of the normalizer `N = N(H)`, and
   `|N| = |H| · |fixed cosets|`.
4. `H` is normal in `N`, so `N / H` is a group, of order `|N| / |H|`, which is
   the number of fixed cosets. So `p` divides `|N / H|`.
5. By Cauchy's theorem, `N / H` has an element `x̄` of order `p`. Its powers form
   a subgroup of order `p`, whose preimage `K` in `N` has `p · |H| = p ^ (k+1)`
   elements.

Steps 3 and 5 both count a preimage under the quotient map, using that each
coset of `H` has `|H|` elements. -/

/-- **Counting preimages.** If `t` is a set of cosets of `H`, then the elements
of `G` lying in those cosets number `|H| · |t|`: each coset has `|H|` elements.

Lean: `QuotientGroup.mk : G → G ⧸ H` sends `x` to its coset `xH`, and
`QuotientGroup.mk ⁻¹' t` is the preimage of `t`. Mathlib's
`preimageMkEquivSubgroupProdSet` is a bijection from that preimage to the
product `H × t`, and `Nat.card_prod` counts a product. -/
theorem card_preimage_mk (H : Subgroup G) (t : Set (G ⧸ H)) :
    Nat.card (QuotientGroup.mk ⁻¹' t : Set G) = Nat.card H * Nat.card t := by
  rw [← Nat.card_prod, Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H t)]

/-- **Fixed cosets.** Let `H` act on its cosets `G ⧸ H` by left
multiplication. The coset `xH` is fixed by every element of `H` exactly when
`x` is in the normalizer of `H`.

Proof. `xH` is fixed when `hxH = xH` for all `h ∈ H`, that is, when
`x⁻¹ h x ∈ H` for all `h ∈ H` (after replacing `h` by `h⁻¹`): in other words,
`x⁻¹ H x ⊆ H`. The normalizer asks for `x⁻¹ H x = H`. As `H` is finite and
conjugation is injective, the inclusion already gives equality.

Lean: `(x : G ⧸ H)` is the coset `xH`. `MulAction.Quotient.smul_mk` computes
`h • xH = (hx)H`, and `QuotientGroup.eq` says `aH = bH ↔ a⁻¹ b ∈ H`. Mathlib's
`mem_normalizer_fintype` is the finiteness argument, and
`mem_normalizer_iff''` says `x ∈ N(H) ↔ ∀ h, (h ∈ H ↔ x⁻¹ h x ∈ H)`. -/
theorem mk_mem_fixedPoints_iff [Finite G] {H : Subgroup G} {x : G} :
    (x : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ H) ↔ x ∈ Subgroup.normalizer (H : Set G) := by
  -- First: "fixed" means `x⁻¹ h x ∈ H` for every `h ∈ H`.
  have key : (x : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ H) ↔ ∀ h ∈ H, x⁻¹ * h * x ∈ H := by
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hx h hh
      -- `h⁻¹ • xH = xH` says `(h⁻¹ x)⁻¹ x ∈ H`, and `(h⁻¹ x)⁻¹ x = x⁻¹ h x`.
      have := hx ⟨h⁻¹, H.inv_mem hh⟩
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at this
      simpa [mul_assoc] using this
    · rintro hx ⟨h, hh⟩
      -- `h • xH = xH` says `(h x)⁻¹ x = x⁻¹ h⁻¹ x ∈ H`: the hypothesis, for `h⁻¹`.
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using hx h⁻¹ (H.inv_mem hh)
  rw [key]
  constructor
  · -- `x⁻¹ H x ⊆ H` puts `x⁻¹` in `N(H)` (by finiteness), and hence `x` too.
    intro hx
    rw [← inv_mem_iff]
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    simpa using hx n hn
  · -- Conversely, the normalizer condition contains `x⁻¹ H x ⊆ H`.
    intro hx h hh
    exact (Subgroup.mem_normalizer_iff''.1 hx h).1 hh

/-- **The growing step.** If `|H| = p ^ k` and `p ^ (k+1) ∣ |G|`, then `G` has a
subgroup of order `p ^ (k+1)`. The steps are numbered as in the plan above.

Lean notation: `set N := …` gives the normalizer a short name. `H.subgroupOf N`,
called `H'` here, is `H` viewed as a subgroup of the group `N`, and `N ⧸ H'` is
the quotient group `N / H`. `exists_prime_orderOf_dvd_card'` is Cauchy's
theorem, and `Subgroup.zpowers x` is the subgroup generated by `x`. -/
theorem exists_card_pow_succ [Finite G] {p : ℕ} [hp : Fact p.Prime] {k : ℕ}
    (hdvd : p ^ (k + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ k) :
    ∃ K : Subgroup G, Nat.card K = p ^ (k + 1) := by
  set N := Subgroup.normalizer (H : Set G)
  set H' := H.subgroupOf N
  -- `H'` is `H` itself, seen inside `N`, so it also has `p ^ k` elements.
  have hH' : Nat.card H' = p ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hH]
  -- Step 1. `|G| = p ^ k · [G : H]` is divisible by `p ^ k · p`, so `p ∣ [G : H]`.
  have h1 : p ∣ H.index := by
    rw [← H.card_mul_index, hH, pow_succ] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos k) hdvd
  -- Step 2. The counting lemma: `|fixed cosets| ≡ |G ⧸ H| = [G : H] ≡ 0 (mod p)`.
  have h2 : p ∣ Nat.card (MulAction.fixedPoints H (G ⧸ H)) := by
    rw [← ((IsPGroup.of_card hH).card_modEq_card_fixedPoints (G ⧸ H)).dvd_iff dvd_rfl,
      ← Subgroup.index_eq_card]
    exact h1
  -- Step 3. The elements of `G` in fixed cosets are exactly the elements of `N`,
  -- so `|N| = |H| · |fixed cosets|`.
  have h3 : Nat.card N = Nat.card H * Nat.card (MulAction.fixedPoints H (G ⧸ H)) := by
    have hpre : (QuotientGroup.mk ⁻¹' MulAction.fixedPoints H (G ⧸ H) : Set G) = N := by
      ext x
      exact mk_mem_fixedPoints_iff
    rw [← card_preimage_mk, hpre]
    rfl
  -- Step 4. Lagrange in `N`: `|N| = |N / H| · |H|`. Comparing with step 3,
  -- `|N / H| = |fixed cosets|`, which `p` divides.
  have h4 : Nat.card (N ⧸ H') = Nat.card (MulAction.fixedPoints H (G ⧸ H)) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup H'
    rw [h3, hH', ← hH, mul_comm] at this
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos this).symm
  -- Step 5. Cauchy's theorem in `N / H` gives `x̄` of order `p`; `K₁` is the
  -- preimage in `N` of the subgroup generated by `x̄`.
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N ⧸ H') p (h4 ▸ h2)
  set K₁ := (Subgroup.zpowers x).comap (QuotientGroup.mk' H')
  -- `K₁` has `|H| · p` elements: `p` cosets of `H`, with `|H|` elements each.
  have h5 : Nat.card K₁ = p ^ k * p := by
    have e1 : Nat.card K₁ =
        Nat.card (QuotientGroup.mk ⁻¹' (Subgroup.zpowers x : Set (N ⧸ H'))) := rfl
    have e2 : Nat.card (Subgroup.zpowers x : Set (N ⧸ H')) = p := by
      show Nat.card (Subgroup.zpowers x) = p
      rw [Nat.card_zpowers, hx]
    rw [e1, card_preimage_mk, hH', e2]
  -- Step 6. `K₁` is a subgroup of `N`. Its image in `G` has the same number of
  -- elements, since the inclusion `N → G` is injective.
  refine ⟨K₁.map N.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective, h5, pow_succ]

/-- **Subgroups of every `p`-power order.** If `p ^ k ∣ |G|`, then `G` has a
subgroup of order `p ^ k`. This is stronger than Sylow I, which is the case
`k = n`.

Proof by induction on `k`. For `k = 0`, take the trivial subgroup `⊥`, of
order `1`. For `k + 1`, the induction hypothesis gives `H` of order `p ^ k`
(since `p ^ k` divides `p ^ (k+1)`, hence `|G|`), and the growing step gives a
subgroup of order `p ^ (k+1)`.

Lean: the lines `| 0, _ => …` and `| k + 1, hdvd => …` are the two cases of the
induction, and the call `exists_card_pow k …` inside the second one is the
induction hypothesis. -/
theorem exists_card_pow [Finite G] {p : ℕ} [Fact p.Prime] :
    ∀ k : ℕ, p ^ k ∣ Nat.card G → ∃ K : Subgroup G, Nat.card K = p ^ k
  | 0, _ => ⟨⊥, by simp⟩
  | k + 1, hdvd => by
    obtain ⟨H, hH⟩ := exists_card_pow k (dvd_trans (pow_dvd_pow p k.le_succ) hdvd)
    exact exists_card_pow_succ hdvd hH

/-- **Sylow I.** `G` has a Sylow `p`-subgroup: take `k = n`, since `p ^ n`
divides `|G|` (`Nat.ordProj_dvd`). -/
theorem exists_isSylowSubgroup [Finite G] {p : ℕ} [Fact p.Prime] :
    ∃ P : Subgroup G, IsSylowSubgroup p P :=
  exists_card_pow _ (Nat.ordProj_dvd _ _)

/-! ### 6.4 Sylow II: conjugacy

Let `P` be a Sylow `p`-subgroup and `Q` any `p`-subgroup. `Q` acts on the
cosets `G ⧸ P` by left multiplication. There are `[G : P]` cosets, and `p` does
not divide `[G : P]`, so by the counting tool some coset `gP` is fixed by `Q`.
That says exactly `Q ⊆ g P g⁻¹`. If `Q` is also a Sylow subgroup, then it has
as many elements as `g P g⁻¹`, so `Q = g P g⁻¹`. -/

/-- **The index of a Sylow subgroup is not divisible by `p`.** If `|P| = p ^ n`
and `p ∣ [G : P]`, then `p ^ (n+1) = p ^ n · p` divides `|P| · [G : P] = |G|`.
That contradicts the choice of `n` as the exponent of `p` in `|G|`.

Lean: `rintro ⟨k, hk⟩` assumes `[G : P] = p * k`. The `calc` block is a chain
of equalities written as on paper; each step carries its own justification. -/
theorem not_dvd_index [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}
    (hP : IsSylowSubgroup p P) : ¬ p ∣ P.index := by
  rintro ⟨k, hk⟩
  apply Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := G)).ne' hp.out
  refine ⟨k, ?_⟩
  calc Nat.card G = Nat.card P * P.index := P.card_mul_index.symm
    _ = p ^ ((Nat.card G).factorization p + 1) * k := by rw [hP, hk, pow_succ, mul_assoc]

/-- **Every `p`-subgroup lies in a conjugate of a Sylow subgroup.**

Lean: `exists_fixedPoint` gives a fixed coset, and `QuotientGroup.mk_surjective`
writes it as `gP` for some `g ∈ G`. For `q ∈ Q`, the fixed-point equation
`q • gP = gP` unfolds, as in `mk_mem_fixedPoints_iff`, to `(qg)⁻¹ g ∈ P`.
Its inverse `g⁻¹ q g` is then in `P` too, which says `q ∈ g P g⁻¹`. -/
theorem exists_le_conjugate [Finite G] {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hP : IsSylowSubgroup p P) (hQ : IsPGroup p Q) : ∃ g : G, Q ≤ conjugate g P := by
  obtain ⟨x, hx⟩ := exists_fixedPoint hQ (G ⧸ P)
    (by rw [← Subgroup.index_eq_card]; exact not_dvd_index hP)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, fun q hq => ?_⟩
  have h := hx ⟨q, hq⟩
  rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
  rw [mem_conjugate]
  simpa [mul_assoc] using P.inv_mem h

/-- **Sylow II.** Two Sylow `p`-subgroups are conjugate.

Lean: `Subgroup.eq_of_le_of_card_ge` says that `Q ≤ K` and `|K| ≤ |Q|` force
`Q = K`. Here `|g P g⁻¹| = |P| = p ^ n = |Q|`. -/
theorem conjugate_of_isSylow [Finite G] {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hP : IsSylowSubgroup p P) (hQ : IsSylowSubgroup p Q) : ∃ g : G, Q = conjugate g P := by
  obtain ⟨g, hg⟩ := exists_le_conjugate hP (IsPGroup.of_card hQ)
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [card_conjugate, hP, hQ]

/-! ### 6.5 Sylow III: counting

`G` acts on the set of its Sylow `p`-subgroups by conjugation, `g • P = g P g⁻¹`.
(A conjugate of a Sylow subgroup has the same order, so it is again a Sylow
subgroup.) Two facts about this action give the two parts of Sylow III.

* **`n_p ≡ 1 (mod p)`.** Restrict the action to one Sylow subgroup `P`. A fixed
  point is a Sylow subgroup `Q` with `x Q x⁻¹ = Q` for all `x ∈ P`, that is,
  with `P ⊆ N(Q)`. Inside the group `N(Q)`, both `P` and `Q` are Sylow
  subgroups, so by Sylow II, `P ⊆ y Q y⁻¹` for some `y ∈ N(Q)`. But `y`
  normalizes `Q`, so `P ⊆ Q`, and then `P = Q`. Hence `P` is the only fixed
  point, and the counting lemma gives `n_p ≡ 1 (mod p)`.
* **`n_p = [G : N(P)]`, which divides `m`.** By Sylow II, the action has a
  single orbit, so orbit–stabilizer gives `n_p = [G : stabilizer of P]`, and
  the stabilizer is `N(P)` by definition of the normalizer. Since `P ≤ N(P)`,
  the index `[G : N(P)]` divides `[G : P] = m`. -/

/-- The action of `G` on its Sylow `p`-subgroups by conjugation.

Lean: an action (`MulAction`) consists of the operation `smul`, written
`g • P`, and the two axioms `1 • P = P` and `(g * h) • P = g • (h • P)`. An
element of `SylowSet p G` is a pair `⟨P, proof⟩`, and `Subtype.ext` reduces an
equality of pairs to an equality of their first parts. -/
instance (p : ℕ) : MulAction G (SylowSet p G) where
  smul g P := ⟨conjugate g P.1, by rw [IsSylowSubgroup, card_conjugate]; exact P.2⟩
  one_smul P := Subtype.ext (conjugate_one P.1)
  mul_smul g h P := Subtype.ext (conjugate_mul g h P.1)

/-- `g • P` is the conjugate `g P g⁻¹`, by definition: the proof is `rfl`. -/
theorem smul_val {p : ℕ} (g : G) (P : SylowSet p G) : (g • P).1 = conjugate g P.1 := rfl

/-- The stabilizer of `P` is its normalizer: `g P g⁻¹ = P` exactly when
`x ∈ P ↔ g⁻¹ x g ∈ P` for all `x`, which is Mathlib's `mem_normalizer_iff''`. -/
theorem stabilizer_eq_normalizer {p : ℕ} (P : SylowSet p G) :
    MulAction.stabilizer G P = Subgroup.normalizer (P.1 : Set G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_normalizer_iff'', Subtype.ext_iff, smul_val,
    SetLike.ext_iff]
  simp only [mem_conjugate]
  exact forall_congr' fun x => Iff.comm

/-- **The key step of Sylow III.** If a Sylow subgroup `P` normalizes a Sylow
subgroup `Q`, then `P = Q`.

Proof. Let `N = N(Q)`. Its order is divisible by `|Q| = p ^ n` and divides
`|G|`, so the exponent of `p` in `|N|` is again `n`: `Q` is a Sylow subgroup of
the group `N`, and `P` is a `p`-subgroup of `N`. Sylow II inside `N` (the
strong form, `exists_le_conjugate`) gives `y ∈ N` with `P ⊆ y Q y⁻¹`, and
`y Q y⁻¹ = Q` because `y` normalizes `Q`. So `P ⊆ Q`, and equal orders give
`P = Q`.

Lean: this applies our own `exists_le_conjugate` to the group `N`, the
normalizer viewed as a group in its own right. `P.subgroupOf N` and
`Q.subgroupOf N` are `P` and `Q` seen inside `N`. Coming back to `G` uses
`Subgroup.mem_subgroupOf`, and the fact that multiplication and inverses in
`N` are those of `G` (`Subgroup.coe_mul`, `Subgroup.coe_inv`). -/
theorem eq_of_le_normalizer [Finite G] {p : ℕ} [hp : Fact p.Prime] {P Q : Subgroup G}
    (hP : IsSylowSubgroup p P) (hQ : IsSylowSubgroup p Q)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) : P = Q := by
  set N := Subgroup.normalizer (Q : Set G)
  have hQN : Q ≤ N := Subgroup.le_normalizer
  -- The exponent of `p` in `|N|` is `n`: `p ^ n = |Q|` divides `|N|`, which divides `|G|`.
  have hcardN : (Nat.card N).factorization p = (Nat.card G).factorization p := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_subgroup_dvd_card N) p
    · rw [← hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne', ← hQ]
      exact Subgroup.card_dvd_of_le hQN
  -- So `Q` is a Sylow subgroup of `N`, and `P` is a `p`-subgroup of `N`.
  have hQ' : IsSylowSubgroup p (Q.subgroupOf N) := by
    rw [IsSylowSubgroup, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv, hcardN]
    exact hQ
  have hP' : IsPGroup p (P.subgroupOf N) := by
    apply IsPGroup.of_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv]
    exact hP
  -- Sylow II inside `N`: `P ⊆ y Q y⁻¹` for some `y ∈ N`.
  obtain ⟨y, hy⟩ := exists_le_conjugate hQ' hP'
  -- Back in `G`: each `x ∈ P` has `y⁻¹ x y ∈ Q`, so `x ∈ Q`, because `y ∈ N(Q)`.
  have hle : P ≤ Q := by
    intro x hx
    have h1 : (⟨x, hPQ hx⟩ : N) ∈ conjugate y (Q.subgroupOf N) :=
      hy (Subgroup.mem_subgroupOf.2 hx)
    rw [mem_conjugate, Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact (Subgroup.mem_normalizer_iff''.1 y.2 x).2 h1
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP, hQ])

/-- **`P` has exactly one fixed point: `P` itself.**

Lean: `Nat.card_eq_one_iff_exists` says that a type has one element when some
`a` equals every `b`. Our `a` is `P`, which is fixed because conjugating `P` by
its own elements changes nothing (`conjugate_eq_self`). Every fixed `Q` equals
`P` by `eq_of_le_normalizer`. The two uses of `Subtype.ext` peel off two
layers of pairs: a fixed point is a pair (a Sylow subgroup, a proof that it is
fixed), and a Sylow subgroup is a pair (a subgroup, a proof that it is
Sylow). -/
theorem card_fixedPoints [Finite G] {p : ℕ} [Fact p.Prime] (P : SylowSet p G) :
    Nat.card (MulAction.fixedPoints P.1 (SylowSet p G)) = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨P, ?_⟩, ?_⟩
  · rw [MulAction.mem_fixedPoints]
    rintro ⟨x, hx⟩
    exact Subtype.ext (conjugate_eq_self hx)
  · rintro ⟨Q, hQ⟩
    apply Subtype.ext
    apply Subtype.ext
    symm
    apply eq_of_le_normalizer P.2 Q.2
    intro x hx
    -- `Q` is fixed by `x`, so `x Q x⁻¹ = Q`, which puts `x` in the normalizer of `Q`.
    have hconj : conjugate x Q.1 = Q.1 :=
      congrArg Subtype.val ((MulAction.mem_fixedPoints.1 hQ) ⟨x, hx⟩)
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    rw [← mem_conjugate, hconj]

/-- **Sylow III, first part: `n_p ≡ 1 (mod p)`.** The counting lemma, for a
Sylow subgroup `P` acting on all the Sylow subgroups:
`n_p ≡ |fixed points| = 1 (mod p)`. -/
theorem card_sylow_modEq_one [Finite G] {p : ℕ} [Fact p.Prime] :
    numSylow p G ≡ 1 [MOD p] := by
  obtain ⟨P, hP⟩ := exists_isSylowSubgroup (G := G) (p := p)
  have := (IsPGroup.of_card hP).card_modEq_card_fixedPoints (SylowSet p G)
  rwa [card_fixedPoints ⟨P, hP⟩] at this

/-- **`n_p = [G : N(P)]`.** By orbit–stabilizer, `[G : stabilizer of P]` is the
size of the orbit of `P`. By Sylow II the orbit is everything, and the
stabilizer is the normalizer.

Lean: `MulAction.index_stabilizer` states orbit–stabilizer with `Set.ncard`,
the number of elements of a set, and `Set.ncard_univ` says that the set of all
Sylow subgroups has `Nat.card (SylowSet p G)` elements. -/
theorem card_sylow_eq_index_normalizer [Finite G] {p : ℕ} [Fact p.Prime] (P : SylowSet p G) :
    numSylow p G = (Subgroup.normalizer (P.1 : Set G)).index := by
  rw [← stabilizer_eq_normalizer, MulAction.index_stabilizer]
  -- Sylow II: every Sylow subgroup `Q` is in the orbit of `P`.
  have horbit : MulAction.orbit G P = Set.univ := by
    ext Q
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := conjugate_of_isSylow P.2 Q.2
    exact ⟨g, Subtype.ext hg.symm⟩
  rw [horbit, Set.ncard_univ]
  rfl

/-- **Sylow III, second part: `n_p ∣ m`.** `n_p = [G : N(P)]` divides
`[G : P]`, because `P ≤ N(P)` (`Subgroup.index_dvd_of_le`), and
`[G : P] = |G| / |P| = m` by Lagrange. -/
theorem card_sylow_dvd [Finite G] {p : ℕ} [Fact p.Prime] :
    numSylow p G ∣ Nat.card G / p ^ (Nat.card G).factorization p := by
  obtain ⟨P, hP⟩ := exists_isSylowSubgroup (G := G) (p := p)
  rw [card_sylow_eq_index_normalizer ⟨P, hP⟩]
  have hidx : P.index = Nat.card G / p ^ (Nat.card G).factorization p := by
    rw [← hP, ← P.card_mul_index, Nat.mul_div_cancel_left _ Nat.card_pos]
  rw [← hidx]
  exact Subgroup.index_dvd_of_le Subgroup.le_normalizer

end Proofs

/-! ### 6.6 The statements of §1

Each statement assumes `Finite G` and `p.Prime` as ordinary hypotheses. The
theorems above take them as *instances*, written in square brackets, which
Lean supplies automatically. A hypothesis `Finite G` already is one, and
`Fact.mk hp` turns `hp : p.Prime` into one. -/

theorem sylowI (p : ℕ) (G : Type*) [Group G] : SylowI p G := fun _ hp =>
  haveI := Fact.mk hp
  exists_isSylowSubgroup

theorem sylowII (p : ℕ) (G : Type*) [Group G] : SylowII p G := fun _ hp _ _ hP hQ =>
  haveI := Fact.mk hp
  conjugate_of_isSylow hP hQ

theorem sylowIII (p : ℕ) (G : Type*) [Group G] : SylowIII p G := fun _ hp =>
  haveI := Fact.mk hp
  ⟨card_sylow_modEq_one, card_sylow_dvd⟩

/-! ## 7. Axiom check

Show this for every main theorem in your presentation. -/

#print axioms sylowI
#print axioms sylowII
#print axioms sylowIII

/-! Each line reports `[propext, Classical.choice, Quot.sound]`: the three
standard axioms, and no `sorryAx`.

A second check, beyond axioms. The proofs must not use Mathlib's own Sylow
theorems, or this file would be circular as an exercise. The command below
follows every definition and theorem that the three proofs depend on, all the
way down, and lists those that come from `Mathlib/GroupTheory/Sylow.lean`. The
list is empty. (The code is meta-programming, which the seminar does not
cover: read it as a tool.) -/

open Lean in
#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : List Name := [``sylowI, ``sylowII, ``sylowIII]
  let mut found : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some i := env.getModuleIdxFor? n then
      if env.header.moduleNames[i.toNat]! == `Mathlib.GroupTheory.Sylow then
        found := found.push n
    if let some c := env.find? n then
      for d in c.getUsedConstantsAsSet do
        todo := d :: todo
  logInfo m!"{seen.size} declarations checked; from Mathlib's Sylow file: {found}"

end Projects.Example
