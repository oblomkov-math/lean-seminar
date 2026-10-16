# Reading `Sylow.lean`

A guided walk through [`Sylow.lean`](Sylow.lean), to read next to VS Code. It
follows the format of [`ReadingLagrange.md`](ReadingLagrange.md) and builds on
it, so read that one first. Its section *How to read Lean* explains statements,
brackets and the InfoView, and its phrasebook covers the tactics used there.
This page explains what is new.

Each stop gives the line numbers, the mathematics on paper, and then the Lean
step by step, with what the InfoView shows after each line. On GitHub, every
line number links to that line of the file.

In VS Code:

- **Cmd+Shift+Enter** shows the InfoView.
- **Ctrl+G** jumps to a line number.
- Hover over a name to see its statement.
- **Cmd**-click a name to open where it is defined; **Ctrl+-** comes back.

The line numbers and the InfoView text below are taken from the file as it
compiles with Lean 4.34 and the seminar's Mathlib. The InfoView blocks show only
the lines that change, and the goal.

## Contents

- [The file at a glance](#the-file-at-a-glance)
- [How the proof fits together](#how-the-proof-fits-together)
- [Stop 1. The problem](#stop-1-the-problem), lines 34–60
- [Stop 2. The statement](#stop-2-the-statement), lines 62–108
- [Stop 3. The checks](#stop-3-the-checks), lines 110–175
- [Stop 4. The tools and the plan](#stop-4-the-tools-and-the-plan), lines 177–214
- [Stop 5. Conjugate subgroups](#stop-5-conjugate-subgroups), lines 216–258
- [Stop 6. The counting tool](#stop-6-the-counting-tool), lines 260–291
- [Stop 7. Sylow I, two lemmas about cosets](#stop-7-sylow-i-two-lemmas-about-cosets), lines 293–363
- [Stop 8. Sylow I, the growing step](#stop-8-sylow-i-the-growing-step), lines 365–418
- [Stop 9. Sylow I, induction](#stop-9-sylow-i-induction), lines 420–443
- [Stop 10. Sylow II](#stop-10-sylow-ii), lines 445–492
- [Stop 11. Sylow III, the action on Sylow subgroups](#stop-11-sylow-iii-the-action-on-sylow-subgroups), lines 494–533
- [Stop 12. Sylow III, the key step](#stop-12-sylow-iii-the-key-step), lines 535–580
- [Stop 13. Sylow III, the count](#stop-13-sylow-iii-the-count), lines 582–649
- [Stop 14. The statements of §1](#stop-14-the-statements-of-1), lines 653–670
- [Stop 15. The checks at the end](#stop-15-the-checks-at-the-end), lines 672–707
- [Phrasebook additions](#phrasebook-additions)

## The file at a glance

The file follows the seminar's project template. Each bar shows where a part
sits among the 709 lines, to scale: one character is about twelve lines.

```text
Header and imports    1–32   ░░░·························································
§0 The problem       34–60   ···██·······················································
§1 Statement         62–108  ·····████···················································
§2 Prerequisites    110–134  ·········▒▒·················································
§3 Vacuity guard    136–157  ···········▒▒···············································
§4 Junk values      159–175  ·············▒▒·············································
§5 Proof route      177–189  ···············█············································
§6 The plan         191–214  ················██··········································
§6.1 Conjugates     216–258  ··················████······································
§6.2 Counting tool  260–291  ······················███···································
§6.3 Sylow I        293–443  ·························████████████·······················
§6.4 Sylow II       445–492  ······································████··················
§6.5 Sylow III      494–649  ··········································█████████████·····
§6.6 Assembly       653–670  ·······················································██···
§7 Axiom check      672–707  ·························································▒▒▒
```

█ the mathematics, to read first · ▒ the template's checks, to read once after
the proof · ░ setup

On a first pass, read §0 and §1, then §6.6 at the end of §6, which shows how
the three theorems come out of the lemmas. Then read §6 in order. Sylow II, in
§6.4, has the shortest proof and does not depend on §6.3, so it also makes a
good first proof to read.

## How the proof fits together

Each theorem rests on the lemmas listed under it. The numbers link to the
statements.

- **Sylow I**, `sylowI`, line [660](Sylow.lean#L660)
  - `exists_isSylowSubgroup`, line [441](Sylow.lean#L441): the case k = n of the next lemma.
    - `exists_card_pow`, line [432](Sylow.lean#L432): a subgroup of order p^k
      whenever p^k divides |G|, by induction on k.
      - `exists_card_pow_succ`, line [372](Sylow.lean#L372): the growing step,
        from order p^k to order p^(k+1).
        - `card_preimage_mk`, line [321](Sylow.lean#L321), and
          `mk_mem_fixedPoints_iff`, line [338](Sylow.lean#L338).
- **Sylow II**, `sylowII`, line [664](Sylow.lean#L664)
  - `conjugate_of_isSylow`, line [488](Sylow.lean#L488)
    - `exists_le_conjugate`, line [473](Sylow.lean#L473): every p-subgroup
      lies in a conjugate of a given Sylow subgroup.
      - `exists_fixedPoint`, line [284](Sylow.lean#L284), and
        `not_dvd_index`, line [459](Sylow.lean#L459).
- **Sylow III**, `sylowIII`, line [668](Sylow.lean#L668)
  - `card_sylow_modEq_one`, line [614](Sylow.lean#L614): n_p ≡ 1 (mod p).
    - `card_fixedPoints`, line [591](Sylow.lean#L591): a Sylow subgroup P,
      acting by conjugation, fixes only itself.
      - `eq_of_le_normalizer`, line [550](Sylow.lean#L550), which applies
        `exists_le_conjugate` inside a normalizer.
  - `card_sylow_dvd`, line [642](Sylow.lean#L642): n_p divides m.
    - `card_sylow_eq_index_normalizer`, line [627](Sylow.lean#L627):
      n_p = [G : N(P)], which uses Sylow II.

The small facts about conjugate subgroups in §6.1 are used throughout.

## Stop 1. The problem

**§0, lines [34–60](Sylow.lean#L34-L60).** The three theorems as a textbook
states them. Write |G| = p^n · m with p ∤ m. A Sylow p-subgroup is a subgroup of
order p^n. Then (1) G has one; (2) any two are conjugate; (3) their number n_p
satisfies n_p ≡ 1 (mod p) and n_p ∣ m.

Below it, the file records four decisions:

- n is the exponent of p in |G|, which Lean writes `(Nat.card G).factorization p`.
  If p ∤ |G|, then n = 0, and the trivial subgroup is a Sylow subgroup.
- A Sylow subgroup is defined by its order, as in textbooks. Mathlib defines it
  differently, as a maximal p-subgroup; §2 checks that the two agree.
- Q is conjugate to P if Q = gPg⁻¹ for some g ∈ G.
- n_p counts subgroups, not elements.

## Stop 2. The statement

**§1, lines [62–108](Sylow.lean#L62-L108).** Four definitions supply the
vocabulary, and three more state the theorems.

```lean
def IsSylowSubgroup {G : Type*} [Group G] (p : ℕ) (P : Subgroup G) : Prop :=
  Nat.card P = p ^ (Nat.card G).factorization p
```

Line [75](Sylow.lean#L75). *P is a Sylow p-subgroup* means |P| = p^n, where n is
the exponent of p in |G|. The type `Prop` says that this defines a property,
true or false for each P.

```lean
def conjugate {G : Type*} [Group G] (g : G) (P : Subgroup G) : Subgroup G :=
  P.map (MulAut.conj g).toMonoidHom
```

Line [80](Sylow.lean#L80). gPg⁻¹, defined as the image of P under the
automorphism x ↦ gxg⁻¹, which Mathlib calls `MulAut.conj g`. `P.map f` is the
image of the subgroup P under the homomorphism f, and `.toMonoidHom` views the
automorphism as a homomorphism.

```lean
abbrev SylowSet (p : ℕ) (G : Type*) [Group G] : Type _ :=
  {P : Subgroup G // IsSylowSubgroup p P}
```

Line [85](Sylow.lean#L85). The set of Sylow p-subgroups, made into a type so
that it can be counted and acted on. An element is a pair ⟨P, h⟩: a subgroup P,
with a proof h that P is Sylow. For such a pair `P`, Lean writes `P.1` for the
subgroup and `P.2` for the proof; §6.5 uses this often. (`abbrev` is a `def`
that Lean unfolds freely.)

```lean
noncomputable def numSylow (p : ℕ) (G : Type*) [Group G] : ℕ :=
  Nat.card (SylowSet p G)
```

Line [91](Sylow.lean#L91). n_p, the number of Sylow p-subgroups.

```lean
def SylowI (p : ℕ) (G : Type*) [Group G] : Prop :=
  Finite G → p.Prime → ∃ P : Subgroup G, IsSylowSubgroup p P
```

Line [95](Sylow.lean#L95). *If G is finite and p is prime, then G has a Sylow
p-subgroup.* Each arrow → reads *if … then*, with the hypotheses in order.

```lean
def SylowII (p : ℕ) (G : Type*) [Group G] : Prop :=
  Finite G → p.Prime → ∀ P Q : Subgroup G, IsSylowSubgroup p P → IsSylowSubgroup p Q →
    ∃ g : G, Q = conjugate g P
```

Line [100](Sylow.lean#L100). *If G is finite and p is prime, then for all
subgroups P and Q that are Sylow p-subgroups, Q = gPg⁻¹ for some g.*

```lean
def SylowIII (p : ℕ) (G : Type*) [Group G] : Prop :=
  Finite G → p.Prime →
    numSylow p G ≡ 1 [MOD p] ∧ numSylow p G ∣ Nat.card G / p ^ (Nat.card G).factorization p
```

Line [106](Sylow.lean#L106). *If G is finite and p is prime, then n_p ≡ 1
(mod p) and n_p divides m = |G|/p^n.* The sign `∧` is *and*, and
`a ≡ b [MOD p]` is a ≡ b (mod p).

As in the Lagrange file, these are definitions of type `Prop`. They name the
statements, and §6.6 proves them after the lemmas.

## Stop 3. The checks

**§2–§4, lines [110–175](Sylow.lean#L110-L175).** Skim these now, and read them
properly after the proof.

**§2, lines [110–134](Sylow.lean#L110-L134).** The `#check` lines pair each
object in §1 with its Mathlib declaration. Then lines
[129–132](Sylow.lean#L129-L132) check that `IsSylowSubgroup` agrees with
Mathlib's own notion, the type `Sylow p G` of maximal p-subgroups:

```lean
example {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Subgroup G) :
    IsSylowSubgroup p P ↔ ∃ S : Sylow p G, (S : Subgroup G) = P :=
  ⟨fun h => ⟨Sylow.ofCard P h, Sylow.coe_ofCard P h⟩,
    fun ⟨S, hS⟩ => hS ▸ S.card_eq_multiplicity⟩
```

The proof is a pair of functions, one for each direction of the ↔. For ⇒,
given `h`, Mathlib's `Sylow.ofCard` turns P into a Sylow subgroup in Mathlib's
sense, and `Sylow.coe_ofCard` says that it is still P. For ⇐, given S with
`hS : S = P`, Mathlib's `S.card_eq_multiplicity` says that S has order p^n, and
`hS ▸` rewrites S as P. This is the only use of Mathlib's Sylow theory in the
file.

**§3, lines [136–157](Sylow.lean#L136-L157).** The hypotheses can be met: S₃ is
finite and 3 is prime (line [146](Sylow.lean#L146)). Lines
[148–157](Sylow.lean#L148-L157) then confirm that A₃ is a Sylow 3-subgroup of
S₃:

- **Line [151](Sylow.lean#L151), `have h6 : … = 2 * 3 := by simp; rfl`.**
  |S₃| = 2 · 3. `simp` turns the goal into `Fintype.card (Equiv.Perm (Fin 3)) = 6`,
  and `rfl` makes Lean compute the left side.
- **Lines [153–154](Sylow.lean#L153-L154), `have h3 : … = 3`.** |A₃| = 3.
  `decide` lists the six permutations and counts the even ones.
- **Line [156](Sylow.lean#L156), four rewrites.** Put the cursor after each
  comma to watch them:

  ```text
  ⊢ Nat.card ↥(alternatingGroup (Fin 3)) = 3 ^ (Nat.card (Equiv.Perm (Fin 3))).factorization 3
  ⊢ Nat.card ↥(alternatingGroup (Fin 3)) = 3 ^ (2 * 3).factorization 3
  ⊢ 3 = 3 ^ (2 * 3).factorization 3
  ⊢ 3 = 3 ^ (Nat.factorization 2 + Nat.factorization 3) 3
  ```

  The last rule, `Nat.factorization_mul`, says that the exponents of a product
  are the sums of the exponents. Lean treats a factorization as a function, and
  the final `3` applies it to the prime 3. The two `(by norm_num)` arguments
  prove 2 ≠ 0 and 3 ≠ 0.
- **Line [157](Sylow.lean#L157).** `simp`, given the factorizations of the
  primes 2 and 3, computes the exponent 0 + 1 = 1. *No goals.*

**§4, lines [159–175](Sylow.lean#L159-L175).** The junk values. `Nat.card` of an
infinite set is 0, `factorization` at a number that is not prime is 0, and
division on ℕ rounds down. So every statement assumes `Finite G` and
`p.Prime`; and since p^n divides |G|, `Nat.card G / p ^ n` is exactly m.

## Stop 4. The tools and the plan

**§5, lines [177–189](Sylow.lean#L177-L189).** The four facts from Mathlib that
carry the proofs:

- Line [182](Sylow.lean#L182), `Subgroup.card_mul_index`: Lagrange's theorem,
  |H| · [G : H] = |G|.
- Line [185](Sylow.lean#L185), `IsPGroup.card_modEq_card_fixedPoints`: if a
  p-group acts on a finite set X, then |X| ≡ |fixed points| (mod p).
- Line [187](Sylow.lean#L187), `exists_prime_orderOf_dvd_card'`: Cauchy's
  theorem, that G has an element of order p when p ∣ |G|.
- Line [189](Sylow.lean#L189), `MulAction.index_stabilizer`: orbit–stabilizer.

**§6, lines [191–209](Sylow.lean#L191-L209)** states the plan of the proof, one
item per subsection. Read it before going on. Lines
[211–214](Sylow.lean#L211-L214) open `section Proofs` with
`variable {G : Type*} [Group G]`: *from here on, G is a group*.

## Stop 5. Conjugate subgroups

**§6.1, lines [216–258](Sylow.lean#L216-L258).** Five small facts about gPg⁻¹.

### `mem_conjugate`, lines 223–225

> **Lemma.** x ∈ gPg⁻¹ ⟺ g⁻¹xg ∈ P.

The proof is one line of three rewrites, line [225](Sylow.lean#L225). With the
cursor after each rule:

```text
⊢ x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) P ↔ g⁻¹ * x * g ∈ P
⊢ (MulEquiv.symm (MulAut.conj g)) x ∈ P ↔ g⁻¹ * x * g ∈ P
No goals
```

`conjugate` unfolds the definition. `Subgroup.mem_map_equiv` says that x lies in
the image of P under an isomorphism f exactly when f⁻¹(x) ∈ P; Lean writes the
inverse of f as `MulEquiv.symm f`. `MulAut.conj_symm_apply` computes that
inverse, x ↦ g⁻¹xg. Both sides are then the same, and `rw` closes the goal by
itself.

### `card_conjugate`, lines 228–230

> **Lemma.** |gPg⁻¹| = |P|.

A proof in one expression, like `card_coset` in the Lagrange file.
`Subgroup.card_map_of_injective` says that an injective homomorphism does not
change the size of a subgroup, and `(MulAut.conj g).injective` says that
conjugation by g is injective.

### `conjugate_one` and `conjugate_mul`, lines 236–245

> **Lemma.** 1P1⁻¹ = P, and (gh)P(gh)⁻¹ = g(hPh⁻¹)g⁻¹.

Both proofs are `ext x` followed by `simp`. After `ext x` on line
[244](Sylow.lean#L244):

```text
x : G
⊢ x ∈ conjugate (g * h) P ↔ x ∈ conjugate g (conjugate h P)
```

`simp [mem_conjugate, mul_assoc]` rewrites both sides with `mem_conjugate` and
finishes with the group laws. These two facts are the axioms of a group action,
which Stop 11 needs.

### `conjugate_eq_self`, lines 249–258

> **Lemma.** If g ∈ P, then gPg⁻¹ = P.
>
> **Proof.** If g⁻¹xg ∈ P, then x = g(g⁻¹xg)g⁻¹ ∈ P. If x ∈ P, then g⁻¹xg is a
> product of three elements of P.

- **Lines [250–251](Sylow.lean#L250-L251), `ext x`, then `rw [mem_conjugate]`.**

  ```text
  ⊢ g⁻¹ * x * g ∈ P ↔ x ∈ P
  ```

- **Lines [252–254](Sylow.lean#L252-L254), `constructor`, then `intro h`.**

  ```text
  case mp
  h : g⁻¹ * x * g ∈ P
  ⊢ x ∈ P
  ```

- **Line [255](Sylow.lean#L255), `simpa [mul_assoc] using P.mul_mem (P.mul_mem hg h) (P.inv_mem hg)`.**
  The term after `using` proves g · (g⁻¹xg) · g⁻¹ ∈ P, by closure under
  products and inverses. `simpa [mul_assoc] using e` simplifies both `e` and
  the goal until they match; here it simplifies g(g⁻¹xg)g⁻¹ to x.
- **Lines [256–258](Sylow.lean#L256-L258).** The other direction, directly.
  `P.mul_mem` multiplies two elements at a time, so it appears twice for a
  product of three.

## Stop 6. The counting tool

**§6.2, lines [260–291](Sylow.lean#L260-L291).**

> **Lemma.** If a p-group H acts on a finite set X and p ∤ |X|, then some a ∈ X
> is fixed by every element of H.
>
> **Proof.** |X| ≡ |fixed points| (mod p), so p does not divide the number of
> fixed points either. In particular, that number is not 0.

The statement, lines [284–286](Sylow.lean#L284-L286), has more hypotheses than
any so far:

```lean
theorem exists_fixedPoint {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] (hH : IsPGroup p H)
    (X : Type*) [MulAction H X] [Finite X] (hX : ¬ p ∣ Nat.card X) :
    ∃ a : X, ∀ h : H, h • a = a := by
```

Read it as: *Let p be prime, and let H be a group that is a p-group (`hH`).
Let X be a finite set on which H acts (`[MulAction H X]`), and suppose that
p ∤ |X| (`hX`). Then there is a ∈ X with h • a = a for all h ∈ H.* `Fact p.Prime`
is *p is prime*, packaged so that it can sit in square brackets. `h • a` is h
acting on a.

- **Lines [287–288](Sylow.lean#L287-L288), `have hfix : ¬ p ∣ Nat.card (MulAction.fixedPoints H X) := by`, then `rwa [← (hH.card_modEq_card_fixedPoints X).dvd_iff dvd_rfl]`.**
  The claim: p does not divide the number of fixed points.
  `hH.card_modEq_card_fixedPoints X` is the congruence
  |X| ≡ |fixed points| (mod p), and `.dvd_iff dvd_rfl` turns it into
  *p ∣ |X| ⟺ p ∣ |fixed points|*. Rewriting with this from right to left
  turns the claim into the following, which the InfoView shows at the end of
  line 288:

  ```text
  ⊢ ¬p ∣ Nat.card X
  ```

  That is exactly the hypothesis `hX`. The final `a` of `rwa` means *then finish
  with a hypothesis*, and it does.
- **Line [289](Sylow.lean#L289), `rcases isEmpty_or_nonempty (MulAction.fixedPoints H X) with h | ⟨⟨a, ha⟩⟩`.**
  Two cases: the set of fixed points is empty, or it has an element. The
  pattern after `with` names what each case provides, and `|` separates the
  cases. `inl` and `inr` are the left and right sides of the *or*.

  ```text
  case inl
  h : IsEmpty ↑(MulAction.fixedPoints H X)
  ⊢ ∃ a, ∀ (h : H), h • a = a

  case inr
  a : X
  ha : a ∈ MulAction.fixedPoints H X
  ⊢ ∃ a, ∀ (h : H), h • a = a
  ```

- **Line [290](Sylow.lean#L290), `· simp at hfix`.** If there are no fixed
  points, their number is 0, and p divides 0. `simp` turns `hfix` into *False*,
  which closes the case.
- **Line [291](Sylow.lean#L291), `· exact ⟨a, MulAction.mem_fixedPoints.1 ha⟩`.**
  Otherwise, `a` is the answer. `MulAction.mem_fixedPoints` says what
  membership in the fixed points means, and `.1` takes its ⇒ direction: for all
  h, h • a = a.

## Stop 7. Sylow I, two lemmas about cosets

**§6.3, lines [293–363](Sylow.lean#L293-L363).** Read the plan in lines
[295–312](Sylow.lean#L295-L312) first. The growing step of Stop 8 needs two
facts about the cosets of a subgroup H.

In Lean, `G ⧸ H` is the set of left cosets of H; the symbol is typed `\quot`.
`QuotientGroup.mk : G → G ⧸ H` sends x to its coset xH, and
`(x : G ⧸ H)`, which the InfoView shows as `↑x`, is the coset xH. H acts on
G ⧸ H by left multiplication: h • xH = (hx)H.

### `card_preimage_mk`, lines 321–323

> **Lemma.** If t is a set of cosets of H, the elements of G lying in those
> cosets number |H| · |t|.

```lean
theorem card_preimage_mk (H : Subgroup G) (t : Set (G ⧸ H)) :
    Nat.card (QuotientGroup.mk ⁻¹' t : Set G) = Nat.card H * Nat.card t := by
  rw [← Nat.card_prod, Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H t)]
```

`f ⁻¹' t` is the preimage of t under f. The first rule, read from right to left,
turns |H| · |t| into the size of the product H × t:

```text
⊢ Nat.card ↑(QuotientGroup.mk ⁻¹' t) = Nat.card (↥H × ↑t)
```

Mathlib's `QuotientGroup.preimageMkEquivSubgroupProdSet H t` is a bijection
between the preimage and H × t, and `Nat.card_congr` turns it into equal sizes.
*No goals.*

### `mk_mem_fixedPoints_iff`, lines 338–363

> **Lemma.** The coset xH is fixed by every element of H exactly when
> x ∈ N(H).
>
> **Proof.** xH is fixed when hxH = xH for all h ∈ H, that is, when x⁻¹hx ∈ H
> for all h ∈ H: in other words, x⁻¹Hx ⊆ H. The normalizer asks for
> x⁻¹Hx = H. Since H is finite and conjugation is injective, the inclusion
> already gives equality.

The goal at the start:

```text
⊢ ↑x ∈ MulAction.fixedPoints (↥H) (G ⧸ H) ↔ x ∈ Subgroup.normalizer ↑H
```

The proof first proves a key equivalence, lines 341–352, and then the lemma
from it.

- **Line [341](Sylow.lean#L341), `have key : … ↔ ∀ h ∈ H, x⁻¹ * h * x ∈ H := by`.**
  The claim: xH is fixed exactly when x⁻¹hx ∈ H for every h ∈ H.
- **Line [342](Sylow.lean#L342), `rw [MulAction.mem_fixedPoints]`.** Unfold
  *fixed*:

  ```text
  ⊢ (∀ (m : ↥H), m • ↑x = ↑x) ↔ ∀ h ∈ H, x⁻¹ * h * x ∈ H
  ```

- **Lines [343–344](Sylow.lean#L343-L344), `constructor`, then `intro hx h hh`.**
  For ⇒, assume xH is fixed (`hx`), and let h ∈ H.

  ```text
  case mp
  hx : ∀ (m : ↥H), m • ↑x = ↑x
  h : G
  hh : h ∈ H
  ⊢ x⁻¹ * h * x ∈ H
  ```

- **Line [346](Sylow.lean#L346), `have := hx ⟨h⁻¹, H.inv_mem hh⟩`.** Apply `hx`
  to h⁻¹. An element of H is a pair: an element of G, and a proof that it lies
  in H. A fact proved by `have` without a name is called `this`.

  ```text
  this : ⟨h⁻¹, ⋯⟩ • ↑x = ↑x
  ```

- **Line [347](Sylow.lean#L347), `rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at this`.**
  Four rewrites turn h⁻¹ • xH = xH into a statement about elements. After each
  rule:

  ```text
  this : ↑⟨h⁻¹, ⋯⟩ • ↑x = ↑x
  this : ↑(↑⟨h⁻¹, ⋯⟩ • x) = ↑x
  this : ↑(↑⟨h⁻¹, ⋯⟩ * x) = ↑x
  this : (↑⟨h⁻¹, ⋯⟩ * x)⁻¹ * x ∈ H
  ```

  In order: an element of H acts as the same element of G; acting on the coset
  xH gives the coset of h⁻¹x; G acts on itself by multiplication; and
  `QuotientGroup.eq` says aH = bH ⟺ a⁻¹b ∈ H.
- **Line [348](Sylow.lean#L348), `simpa [mul_assoc] using this`.** Simplify
  (h⁻¹x)⁻¹x to x⁻¹hx. The ⇒ direction is done.
- **Line [349](Sylow.lean#L349), `· rintro hx ⟨h, hh⟩`.** For ⇐, assume the
  condition (`hx`), and take an element of H, unpacked as h with `hh : h ∈ H`.

  ```text
  case mpr
  hx : ∀ h ∈ H, x⁻¹ * h * x ∈ H
  h : G
  hh : h ∈ H
  ⊢ ⟨h, hh⟩ • ↑x = ↑x
  ```

- **Lines [351–352](Sylow.lean#L351-L352).** The same four rewrites, now on the
  goal, leave `⊢ (↑⟨h, hh⟩ * x)⁻¹ * x ∈ H`, which is (hx)⁻¹x = x⁻¹h⁻¹x ∈ H.
  That is `hx` for h⁻¹, and `simpa` matches the two.
- **Line [353](Sylow.lean#L353), `rw [key]`.** Back to the main goal:

  ```text
  ⊢ (∀ h ∈ H, x⁻¹ * h * x ∈ H) ↔ x ∈ Subgroup.normalizer ↑H
  ```

- **Lines [354–356](Sylow.lean#L354-L356), `constructor`, then `intro hx`.** For
  ⇒, assume x⁻¹Hx ⊆ H.
- **Line [357](Sylow.lean#L357), `rw [← inv_mem_iff]`.** N(H) is a subgroup, so
  it is enough to show that x⁻¹ lies in it:

  ```text
  ⊢ x⁻¹ ∈ Subgroup.normalizer ↑H
  ```

- **Line [358](Sylow.lean#L358), `apply Subgroup.mem_normalizer_fintype`.**
  Mathlib's finiteness argument: in a finite group, gHg⁻¹ ⊆ H already puts g in
  N(H). Here g = x⁻¹:

  ```text
  ⊢ ∀ n ∈ ↑H, x⁻¹ * n * x⁻¹⁻¹ ∈ ↑H
  ```

- **Lines [359–360](Sylow.lean#L359-L360), `intro n hn`, then `simpa using hx n hn`.**
  `simpa` simplifies x⁻¹⁻¹ to x, and then the goal is `hx` applied to n.
- **Lines [361–363](Sylow.lean#L361-L363).** For ⇐,
  `Subgroup.mem_normalizer_iff''` says that x ∈ N(H) exactly when, for all h,
  h ∈ H ⟺ x⁻¹hx ∈ H. (The primes in its name only tell it apart from two
  similar lemmas.) Its `.1` turns `hx` into that condition, and `.1 hh` uses
  the ⇒ half for our h.

## Stop 8. Sylow I, the growing step

**Lines [365–418](Sylow.lean#L365-L418).** The heart of Sylow I.

> **Lemma.** If |H| = p^k and p^(k+1) divides |G|, then G has a subgroup of
> order p^(k+1).
>
> **Proof.** Let N = N(H). (1) p ∣ [G : H]. (2) H acts on G/H; by the counting
> lemma, the number of fixed cosets is ≡ [G : H] ≡ 0 (mod p). (3) The fixed
> cosets are the cosets xH with x ∈ N, so |N| = |H| · (number of fixed cosets).
> (4) H is normal in N, and |N/H| = number of fixed cosets, which p divides.
> (5) By Cauchy's theorem, N/H has an element x̄ of order p; the preimage K₁ of
> ⟨x̄⟩ in N has p · |H| = p^(k+1) elements. (6) The image of K₁ in G is the
> subgroup we want.

The statement is on lines [372–374](Sylow.lean#L372-L374). The InfoView at its
start shows the hypotheses:

```text
hdvd : p ^ (k + 1) ∣ Nat.card G
H : Subgroup G
hH : Nat.card ↥H = p ^ k
⊢ ∃ K, Nat.card ↥K = p ^ (k + 1)
```

### Setting up, lines 375–379

- **Line [375](Sylow.lean#L375), `set N := Subgroup.normalizer (H : Set G)`.**
  Like `let`, `set` gives the normalizer a short name. It also replaces the
  normalizer by N wherever it appears.
- **Line [376](Sylow.lean#L376), `set H' := H.subgroupOf N`.** To Lean, a
  subgroup of G and a subgroup of N are different kinds of object, even with
  the same elements. `H.subgroupOf N` is H seen as a subgroup of N, and
  `N ⧸ H'` will be the quotient group N/H.

  ```text
  N : Subgroup G := Subgroup.normalizer ↑H
  H' : Subgroup ↥N := H.subgroupOf N
  ```

- **Lines [378–379](Sylow.lean#L378-L379), `have hH' : Nat.card H' = p ^ k`.**
  H' has the elements of H, so |H'| = |H| = p^k.
  `Subgroup.subgroupOfEquivOfLe` is the bijection between H' and H; it needs
  H ≤ N, which is `Subgroup.le_normalizer`.

### Step 1, lines 381–383: p ∣ [G : H]

- **Line [382](Sylow.lean#L382), `rw [← H.card_mul_index, hH, pow_succ] at hdvd`.**
  Rewrite the hypothesis `hdvd` using |G| = |H| · [G : H] = p^k · [G : H].
  After each rule:

  ```text
  hdvd : p ^ (k + 1) ∣ Nat.card ↥H * H.index
  hdvd : p ^ (k + 1) ∣ p ^ k * H.index
  hdvd : p ^ k * p ∣ p ^ k * H.index
  ```

- **Line [383](Sylow.lean#L383), `exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos k) hdvd`.**
  Cancel the factor p^k, which is positive. `hp.out` takes the fact that p is
  prime out of `hp : Fact p.Prime`; `.pos` says that then p > 0, and
  `pow_pos … k` that p^k > 0.

### Step 2, lines 385–388: p divides the number of fixed cosets

- **Lines [386–387](Sylow.lean#L386-L387).** The counting congruence for H acting
  on G ⧸ H. H is a p-group because its order is p^k (`IsPGroup.of_card hH`).
  As in Stop 6, `.dvd_iff dvd_rfl` turns the congruence into an equivalence of
  divisibilities, and `Subgroup.index_eq_card` says [G : H] = |G ⧸ H|. After the
  two rules:

  ```text
  ⊢ p ∣ Nat.card (G ⧸ H)
  ⊢ p ∣ H.index
  ```

- **Line [388](Sylow.lean#L388), `exact h1`.** That is step 1.

### Step 3, lines 391–396: |N| = |H| · (number of fixed cosets)

- **Lines [392–394](Sylow.lean#L392-L394), `have hpre : … = N`.** The elements
  of G whose coset is fixed are exactly the elements of N. After `ext x`, this is
  `mk_mem_fixedPoints_iff` from Stop 7.
- **Line [395](Sylow.lean#L395), `rw [← card_preimage_mk, hpre]`.** Write
  |H| · (number of fixed cosets) as the size of a preimage (Stop 7, read from
  right to left), then replace the preimage by N:

  ```text
  ⊢ Nat.card ↥N = Nat.card ↑(QuotientGroup.mk ⁻¹' MulAction.fixedPoints (↥H) (G ⧸ H))
  ⊢ Nat.card ↥N = Nat.card ↑↑N
  ```

- **Line [396](Sylow.lean#L396), `rfl`.** `↥N`, the subgroup N as a type, and
  `↑↑N`, the set N as a type, have the same elements by definition.

### Step 4, lines 399–402: |N/H| = number of fixed cosets

- **Line [400](Sylow.lean#L400), `have := Subgroup.card_eq_card_quotient_mul_card_subgroup H'`.**
  Lagrange's theorem inside N:

  ```text
  this : Nat.card ↥N = Nat.card (↥N ⧸ H') * Nat.card ↥H'
  ```

- **Line [401](Sylow.lean#L401), `rw [h3, hH', ← hH, mul_comm] at this`.** Put
  step 3 on the left, and |H'| = p^k = |H| on the right; `mul_comm` swaps the
  first product. After each rule:

  ```text
  this : Nat.card ↥H * Nat.card ↑(MulAction.fixedPoints (↥H) (G ⧸ H)) = Nat.card (↥N ⧸ H') * Nat.card ↥H'
  this : Nat.card ↥H * Nat.card ↑(MulAction.fixedPoints (↥H) (G ⧸ H)) = Nat.card (↥N ⧸ H') * p ^ k
  this : Nat.card ↥H * Nat.card ↑(MulAction.fixedPoints (↥H) (G ⧸ H)) = Nat.card (↥N ⧸ H') * Nat.card ↥H
  this : Nat.card ↑(MulAction.fixedPoints (↥H) (G ⧸ H)) * Nat.card ↥H = Nat.card (↥N ⧸ H') * Nat.card ↥H
  ```

- **Line [402](Sylow.lean#L402), `exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos this).symm`.**
  Cancel |H| > 0 on the right; `.symm` reverses the resulting equation.

### Step 5, lines 405–414: Cauchy's theorem and the subgroup K₁

- **Line [405](Sylow.lean#L405), `obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N ⧸ H') p (h4 ▸ h2)`.**
  Cauchy's theorem for the group N/H, which `(G := N ⧸ H')` names explicitly.
  It needs p ∣ |N/H|, which is step 2 rewritten with step 4: `h4 ▸ h2`. `obtain`
  unpacks the result, an element x̄ and its order:

  ```text
  x : ↥N ⧸ H'
  hx : orderOf x = p
  ```

- **Line [406](Sylow.lean#L406), `set K₁ := (Subgroup.zpowers x).comap (QuotientGroup.mk' H')`.**
  `Subgroup.zpowers x` is the subgroup ⟨x̄⟩ generated by x̄, and `.comap f` is
  its preimage under the quotient map N → N/H. So K₁ is a subgroup of N.
- **Lines [408–414](Sylow.lean#L408-L414), `have h5 : Nat.card K₁ = p ^ k * p`.**
  `e1`, on lines 409–410, restates |K₁| as the size of a preimage of a set of
  cosets, which holds by definition. `e2`, on lines 411–413, says |⟨x̄⟩| = p:
  `show` restates it for the subgroup ⟨x̄⟩, `Nat.card_zpowers` says that
  |⟨x̄⟩| is the order of x̄, and `hx` says that this order is p. Line
  [414](Sylow.lean#L414) combines them with `card_preimage_mk`. After each rule:

  ```text
  ⊢ Nat.card ↑(QuotientGroup.mk ⁻¹' ↑(Subgroup.zpowers x)) = p ^ k * p
  ⊢ Nat.card ↥H' * Nat.card ↑↑(Subgroup.zpowers x) = p ^ k * p
  ⊢ p ^ k * Nat.card ↑↑(Subgroup.zpowers x) = p ^ k * p
  No goals
  ```

### Step 6, lines 417–418: back to G

- **Line [417](Sylow.lean#L417), `refine ⟨K₁.map N.subtype, ?_⟩`.** The answer
  is the image of K₁ under the inclusion N → G, which Lean calls `N.subtype`.
  `refine` gives the answer now, and `?_` leaves the proof of its order as the
  new goal:

  ```text
  ⊢ Nat.card ↥(Subgroup.map N.subtype K₁) = p ^ (k + 1)
  ```

- **Line [418](Sylow.lean#L418), `rw [Subgroup.card_map_of_injective N.subtype_injective, h5, pow_succ]`.**
  The inclusion is injective, so the image has |K₁| elements; then step 5; then
  p^(k+1) = p^k · p. After each rule:

  ```text
  ⊢ Nat.card ↥K₁ = p ^ (k + 1)
  ⊢ p ^ k * p = p ^ (k + 1)
  No goals
  ```

## Stop 9. Sylow I, induction

**Lines [420–443](Sylow.lean#L420-L443).**

> **Lemma.** If p^k divides |G|, then G has a subgroup of order p^k.
>
> **Proof.** By induction on k, with the growing step of Stop 8.

```lean
theorem exists_card_pow [Finite G] {p : ℕ} [Fact p.Prime] :
    ∀ k : ℕ, p ^ k ∣ Nat.card G → ∃ K : Subgroup G, Nat.card K = p ^ k
  | 0, _ => ⟨⊥, by simp⟩
  | k + 1, hdvd => by
    obtain ⟨H, hH⟩ := exists_card_pow k (dvd_trans (pow_dvd_pow p k.le_succ) hdvd)
    exact exists_card_pow_succ hdvd hH
```

There is no `:= by` after the statement. Instead, each line starting with `|`
gives the proof for one form of k: k = 0, and k + 1. That is a proof by
induction.

- **Line [434](Sylow.lean#L434), `| 0, _ => ⟨⊥, by simp⟩`.** For k = 0, take
  the trivial subgroup ⊥ (typed `\bot`). It has 1 = p⁰ elements, which `simp`
  checks. The `_` ignores the hypothesis p⁰ ∣ |G|, which is not needed.
- **Line [435](Sylow.lean#L435), `| k + 1, hdvd => by`.** For k + 1, with the
  hypothesis `hdvd : p ^ (k + 1) ∣ Nat.card G`.
- **Line [436](Sylow.lean#L436), `obtain ⟨H, hH⟩ := exists_card_pow k (…)`.**
  The call of `exists_card_pow` for k is the induction hypothesis. It needs
  p^k ∣ |G|, which follows from p^k ∣ p^(k+1) ∣ |G| (`pow_dvd_pow` and
  `dvd_trans`). The InfoView does not list the induction hypothesis: it is the
  name `exists_card_pow` itself, which Lean lets the proof use for the smaller
  number k.

  ```text
  H : Subgroup G
  hH : Nat.card ↥H = p ^ k
  ```

- **Line [437](Sylow.lean#L437), `exact exists_card_pow_succ hdvd hH`.** The
  growing step of Stop 8.

Then `exists_isSylowSubgroup`, lines [441–443](Sylow.lean#L441-L443), is Sylow I:
the case k = n of `exists_card_pow`, since p^n divides |G| (`Nat.ordProj_dvd`).
The `_` lets Lean work out k = n from the goal.

## Stop 10. Sylow II

**§6.4, lines [445–492](Sylow.lean#L445-L492).** Read the plan in lines
[447–451](Sylow.lean#L447-L451). This section does not use §6.3.

### `not_dvd_index`, lines 459–465

> **Lemma.** If P is a Sylow subgroup, then p ∤ [G : P].
>
> **Proof.** If [G : P] = pk, then |G| = |P| · [G : P] = p^n · pk = p^(n+1) · k.
> So p^(n+1) ∣ |G|, against the choice of n.

- **Line [461](Sylow.lean#L461), `rintro ⟨k, hk⟩`.** The goal `¬ p ∣ P.index`
  means that p ∣ [G : P] leads to a contradiction. So assume p ∣ [G : P],
  unpacked as [G : P] = p · k, and prove `False`:

  ```text
  k : ℕ
  hk : P.index = p * k
  ⊢ False
  ```

- **Line [462](Sylow.lean#L462), `apply Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := G)).ne' hp.out`.**
  Mathlib's fact that p^(n+1) does not divide |G|, where n is the exponent of p
  in |G|. Its two arguments say |G| ≠ 0 and p is prime. To contradict it, it
  suffices to prove p^(n+1) ∣ |G|:

  ```text
  ⊢ p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G
  ```

- **Line [463](Sylow.lean#L463), `refine ⟨k, ?_⟩`.** Divisibility means
  |G| = p^(n+1) · c for some c. Take c = k:

  ```text
  ⊢ Nat.card G = p ^ ((Nat.card G).factorization p + 1) * k
  ```

- **Lines [464–465](Sylow.lean#L464-L465), `calc`.** A chain of equalities,
  written as on paper. Each line states the next expression and, after `:=`,
  why it equals the one before. The `_` at the start of line 465 stands for
  the previous right side, |P| · [G : P]. The rewrites on line 465, after each
  rule:

  ```text
  ⊢ p ^ (Nat.card G).factorization p * P.index = p ^ ((Nat.card G).factorization p + 1) * k
  ⊢ p ^ (Nat.card G).factorization p * (p * k) = p ^ ((Nat.card G).factorization p + 1) * k
  ⊢ p ^ (Nat.card G).factorization p * (p * k) = p ^ (Nat.card G).factorization p * p * k
  No goals
  ```

### `exists_le_conjugate`, lines 473–482

> **Lemma.** If P is a Sylow subgroup and Q is a p-subgroup, then Q ⊆ gPg⁻¹ for
> some g.
>
> **Proof.** Q acts on G/P, and p ∤ [G : P], so by the counting tool some coset
> gP is fixed by Q: qgP = gP for all q ∈ Q. That says g⁻¹qg ∈ P, that is,
> q ∈ gPg⁻¹.

- **Lines [475–476](Sylow.lean#L475-L476), `obtain ⟨x, hx⟩ := exists_fixedPoint hQ (G ⧸ P)`, with one more argument on line 476.**
  The counting tool of Stop 6, for Q acting on G ⧸ P. The argument on line 476
  proves p ∤ |G ⧸ P|: once |G ⧸ P| is written as [G : P], that is
  `not_dvd_index`.

  ```text
  x : G ⧸ P
  hx : ∀ (h : ↥Q), h • x = x
  ```

- **Line [477](Sylow.lean#L477), `obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x`.**
  Every coset is gP for some g, and `rfl` replaces x by gP everywhere:

  ```text
  g : G
  hx : ∀ (h : ↥Q), h • ↑g = ↑g
  ```

- **Line [478](Sylow.lean#L478), `refine ⟨g, fun q hq => ?_⟩`.** Take this g.
  Q ≤ gPg⁻¹ means that every q ∈ Q lies in gPg⁻¹, and `fun q hq => ?_` starts
  that proof: let q ∈ Q.

  ```text
  q : G
  hq : q ∈ Q
  ⊢ q ∈ conjugate g P
  ```

- **Lines [479–480](Sylow.lean#L479-L480).** Apply `hx` to q, and unfold
  qgP = gP with the four rewrites of Stop 7:

  ```text
  h : (↑⟨q, hq⟩ * g)⁻¹ * g ∈ P
  ```

- **Lines [481–482](Sylow.lean#L481-L482), `rw [mem_conjugate]`, then `simpa [mul_assoc] using P.inv_mem h`.**
  The goal becomes g⁻¹qg ∈ P. The inverse of (qg)⁻¹g is g⁻¹qg, and P is closed
  under inverses.

  ```text
  ⊢ g⁻¹ * q * g ∈ P
  ```

### `conjugate_of_isSylow`, lines 488–492

> **Lemma (Sylow II).** If P and Q are Sylow subgroups, then Q = gPg⁻¹ for some
> g.

- **Line [490](Sylow.lean#L490), `obtain ⟨g, hg⟩ := exists_le_conjugate hP (IsPGroup.of_card hQ)`.**
  Q is a p-group, because its order is a power of p. So Q ⊆ gPg⁻¹ for some g:

  ```text
  g : G
  hg : Q ≤ conjugate g P
  ```

- **Line [491](Sylow.lean#L491), `refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩`.**
  A subgroup contained in another that has no more elements than it equals it
  (`Subgroup.eq_of_le_of_card_ge`). It remains to compare the sizes:

  ```text
  ⊢ Nat.card ↥(conjugate g P) ≤ Nat.card ↥Q
  ```

- **Line [492](Sylow.lean#L492), `rw [card_conjugate, hP, hQ]`.**
  |gPg⁻¹| = |P| = p^n = |Q|. After each rule:

  ```text
  ⊢ Nat.card ↥P ≤ Nat.card ↥Q
  ⊢ p ^ (Nat.card G).factorization p ≤ Nat.card ↥Q
  No goals
  ```

  After the last rule the goal is p^n ≤ p^n, which `rw` closes by itself.

## Stop 11. Sylow III, the action on Sylow subgroups

**§6.5, lines [494–533](Sylow.lean#L494-L533).** Read the plan in lines
[496–509](Sylow.lean#L496-L509).

### The action, lines 517–520

```lean
instance (p : ℕ) : MulAction G (SylowSet p G) where
  smul g P := ⟨conjugate g P.1, by rw [IsSylowSubgroup, card_conjugate]; exact P.2⟩
  one_smul P := Subtype.ext (conjugate_one P.1)
  mul_smul g h P := Subtype.ext (conjugate_mul g h P.1)
```

An `instance` defines something Lean will then supply by itself, here an action
of G on the set of Sylow subgroups (`MulAction`). After `where`, the lines fill
in its parts one by one:

- `smul g P` defines g • P. Here P is a pair, so `P.1` is the subgroup and `P.2`
  the proof that it is Sylow. g • P is the pair of gP.1g⁻¹ and a proof that it
  is Sylow: |gPg⁻¹| = |P| (`card_conjugate`), and P is Sylow (`P.2`).
- `one_smul` is the axiom 1 • P = P, and `mul_smul` is (gh) • P = g • (h • P).
  They are `conjugate_one` and `conjugate_mul` from Stop 5. `Subtype.ext` says
  that two pairs are equal when their first parts are.

### `smul_val` and `stabilizer_eq_normalizer`, lines 523–533

`smul_val`, line [523](Sylow.lean#L523), records that (g • P).1 = gPg⁻¹. It holds
by definition, so the proof is `rfl`.

> **Lemma.** The stabilizer of P is its normalizer N(P).

- **Line [529](Sylow.lean#L529), `ext g`.**

  ```text
  ⊢ g ∈ MulAction.stabilizer G P ↔ g ∈ Subgroup.normalizer ↑↑P
  ```

- **Lines [530–531](Sylow.lean#L530-L531), five rewrites.** After each rule:

  ```text
  ⊢ g • P = P ↔ g ∈ Subgroup.normalizer ↑↑P
  ⊢ g • P = P ↔ ∀ (h : G), h ∈ ↑P ↔ g⁻¹ * h * g ∈ ↑P
  ⊢ ↑(g • P) = ↑P ↔ ∀ (h : G), h ∈ ↑P ↔ g⁻¹ * h * g ∈ ↑P
  ⊢ conjugate g ↑P = ↑P ↔ ∀ (h : G), h ∈ ↑P ↔ g⁻¹ * h * g ∈ ↑P
  ⊢ (∀ (x : G), x ∈ conjugate g ↑P ↔ x ∈ ↑P) ↔ ∀ (h : G), h ∈ ↑P ↔ g⁻¹ * h * g ∈ ↑P
  ```

  In order: g is in the stabilizer when g • P = P; Mathlib's description of the
  normalizer; pairs are equal when their subgroups are; g • P is gPg⁻¹; and
  subgroups are equal when they have the same elements.
- **Line [532](Sylow.lean#L532), `simp only [mem_conjugate]`.**

  ```text
  ⊢ (∀ (x : G), g⁻¹ * x * g ∈ ↑P ↔ x ∈ ↑P) ↔ ∀ (h : G), h ∈ ↑P ↔ g⁻¹ * h * g ∈ ↑P
  ```

- **Line [533](Sylow.lean#L533), `exact forall_congr' fun x => Iff.comm`.** The
  two sides differ only in the order of each ↔. `Iff.comm` says that A ↔ B is
  the same as B ↔ A, and `forall_congr'` applies this under the ∀.

## Stop 12. Sylow III, the key step

**Lines [535–580](Sylow.lean#L535-L580).**

> **Lemma.** If P and Q are Sylow subgroups and P ⊆ N(Q), then P = Q.
>
> **Proof.** Let N = N(Q). The exponent of p in |N| is n, because
> p^n = |Q| divides |N|, which divides |G|. So Q is a Sylow subgroup of N, and P
> is a p-subgroup of N. By Sylow II inside N, P ⊆ yQy⁻¹ for some y ∈ N. But y
> normalizes Q, so yQy⁻¹ = Q, and P ⊆ Q. Equal orders give P = Q.

- **Line [553](Sylow.lean#L553), `set N := Subgroup.normalizer (Q : Set G)`.**
  Note how `set` also rewrites the hypothesis `hPQ`:

  ```text
  N : Subgroup G := Subgroup.normalizer ↑Q
  hPQ : P ≤ N
  ```

- **Line [554](Sylow.lean#L554), `have hQN : Q ≤ N := Subgroup.le_normalizer`.**
  Q lies in its own normalizer.
- **Lines [556–561](Sylow.lean#L556-L561), `have hcardN : …`.** The exponent of p
  in |N| equals the one in |G|.
  - **Line [557](Sylow.lean#L557), `apply le_antisymm`.** Prove an equality of
    numbers as two inequalities:

    ```text
    case a
    ⊢ (Nat.card ↥N).factorization p ≤ (Nat.card G).factorization p

    case a
    ⊢ (Nat.card G).factorization p ≤ (Nat.card ↥N).factorization p
    ```

  - **Lines [558–559](Sylow.lean#L558-L559).** The first: |N| divides |G|
    (Lagrange, `Subgroup.card_subgroup_dvd_card`), and
    `Nat.factorization_le_iff_dvd` turns divisibility into inequalities between
    exponents.
  - **Lines [560–561](Sylow.lean#L560-L561).** The second:
    `pow_dvd_iff_le_factorization` turns the inequality into p^n ∣ |N|, and `hQ`
    from right to left turns p^n into |Q|. After each rule:

    ```text
    ⊢ p ^ (Nat.card G).factorization p ∣ Nat.card ↥N
    ⊢ Nat.card ↥Q ∣ Nat.card ↥N
    ```

    Then |Q| divides |N| because Q ≤ N (`Subgroup.card_dvd_of_le hQN`).
- **Lines [563–565](Sylow.lean#L563-L565), `have hQ' : IsSylowSubgroup p (Q.subgroupOf N)`.**
  Q, seen inside N, is a Sylow subgroup of N. After each rule on line 564:

  ```text
  ⊢ Nat.card ↥(Q.subgroupOf N) = p ^ (Nat.card ↥N).factorization p
  ⊢ Nat.card ↥Q = p ^ (Nat.card ↥N).factorization p
  ⊢ Nat.card ↥Q = p ^ (Nat.card G).factorization p
  ```

  The last is `hQ`.
- **Lines [566–569](Sylow.lean#L566-L569), `have hP' : IsPGroup p (P.subgroupOf N)`.**
  P, seen inside N, is a p-group. `apply IsPGroup.of_card` leaves the goal that
  its order is p^?n, for an exponent ?n not yet known:

  ```text
  case hG
  ⊢ Nat.card ↥(P.subgroupOf N) = p ^ ?n

  case n
  ⊢ ℕ
  ```

  A name with `?` is a placeholder that Lean fills in later. After the rewrite
  on line 568 the first goal is `Nat.card ↥P = p ^ ?n`. Then `exact hP` matches
  it with |P| = p^n, which fills in ?n = n and settles the second goal too.
- **Line [571](Sylow.lean#L571), `obtain ⟨y, hy⟩ := exists_le_conjugate hQ' hP'`.**
  The strong form of Sylow II from Stop 10, applied to the group N:

  ```text
  y : ↥N
  hy : P.subgroupOf N ≤ conjugate y (Q.subgroupOf N)
  ```

- **Lines [573–579](Sylow.lean#L573-L579), `have hle : P ≤ Q`.** Back in G. Let
  x ∈ P.
  - Lines [575–576](Sylow.lean#L575-L576): `h1` says that x, as an element of N,
    lies in yQy⁻¹.
  - Line [577](Sylow.lean#L577): `rw [mem_conjugate, Subgroup.mem_subgroupOf] at h1`
    turns this into y⁻¹xy ∈ Q, with the product still computed in N. After each
    rule:

    ```text
    h1 : y⁻¹ * ⟨x, ⋯⟩ * y ∈ Q.subgroupOf N
    h1 : ↑(y⁻¹ * ⟨x, ⋯⟩ * y) ∈ Q
    ```

  - Line [578](Sylow.lean#L578): `simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1`
    moves the computation to G, since products and inverses in N are those of
    G:

    ```text
    h1 : (↑y)⁻¹ * x * ↑y ∈ Q
    ```

  - Line [579](Sylow.lean#L579): y normalizes Q (`y.2` says y ∈ N), so by
    `mem_normalizer_iff''`, y⁻¹xy ∈ Q gives x ∈ Q.
- **Line [580](Sylow.lean#L580), `exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP, hQ])`.**
  P ⊆ Q and |Q| ≤ |P|, since both orders are p^n.

## Stop 13. Sylow III, the count

**Lines [582–649](Sylow.lean#L582-L649).**

### `card_fixedPoints`, lines 591–609

> **Lemma.** A Sylow subgroup P, acting on the Sylow subgroups by conjugation,
> has exactly one fixed point: P itself.

The goal at the start:

```text
⊢ Nat.card ↑(MulAction.fixedPoints (↥↑P) (SylowSet p G)) = 1
```

- **Line [593](Sylow.lean#L593), `rw [Nat.card_eq_one_iff_exists]`.** A set has
  exactly one element when some x equals every y in it:

  ```text
  ⊢ ∃ x, ∀ (y : ↑(MulAction.fixedPoints (↥↑P) (SylowSet p G))), y = x
  ```

- **Line [594](Sylow.lean#L594), `refine ⟨⟨P, ?_⟩, ?_⟩`.** Take x = P. Two holes
  remain, so two goals: P is fixed, and every fixed point equals P.

  ```text
  case refine_1
  ⊢ P ∈ MulAction.fixedPoints (↥↑P) (SylowSet p G)

  case refine_2
  ⊢ ∀ (y : ↑(MulAction.fixedPoints (↥↑P) (SylowSet p G))), y = ⟨P, ?refine_1⟩
  ```

- **Lines [595–597](Sylow.lean#L595-L597).** P is fixed: for x ∈ P, x • P = P by
  `conjugate_eq_self` from Stop 5.

  ```text
  x : G
  hx : x ∈ ↑P
  ⊢ ⟨x, hx⟩ • P = P
  ```

- **Line [598](Sylow.lean#L598), `rintro ⟨Q, hQ⟩`.** Let Q be a fixed point:

  ```text
  P Q : SylowSet p G
  hQ : Q ∈ MulAction.fixedPoints (↥↑P) (SylowSet p G)
  ⊢ ⟨Q, hQ⟩ = ⟨P, ⋯⟩
  ```

- **Lines [599–600](Sylow.lean#L599-L600), `apply Subtype.ext`, twice.** A fixed
  point is a pair (a Sylow subgroup, a proof that it is fixed), and a Sylow
  subgroup is a pair (a subgroup, a proof that it is Sylow). Each `Subtype.ext`
  peels off one layer:

  ```text
  ⊢ ↑⟨Q, hQ⟩ = ↑⟨P, ⋯⟩
  ⊢ ↑↑⟨Q, hQ⟩ = ↑↑⟨P, ⋯⟩
  ```

- **Lines [601–602](Sylow.lean#L601-L602), `symm`, then `apply eq_of_le_normalizer P.2 Q.2`.**
  Swap the two sides, to P = Q, and apply the key step of Stop 12. It remains
  to show P ⊆ N(Q):

  ```text
  ⊢ ↑P ≤ Subgroup.normalizer ↑↑Q
  ```

- **Lines [603–606](Sylow.lean#L603-L606).** Let x ∈ P. Q is fixed by x, so
  `hconj` says xQx⁻¹ = Q. Here `congrArg Subtype.val` takes the subgroup part of
  the equation x • Q = Q.

  ```text
  hconj : conjugate x ↑Q = ↑Q
  ```

- **Lines [607–609](Sylow.lean#L607-L609).** Unfold the normalizer, as in
  Stop 7, and let h ∈ G:

  ```text
  ⊢ h ∈ ↑Q ↔ x⁻¹ * h * x ∈ ↑Q
  ```

  `rw [← mem_conjugate, hconj]` reads x⁻¹hx ∈ Q as h ∈ xQx⁻¹, and then replaces
  xQx⁻¹ by Q. After each rule:

  ```text
  ⊢ h ∈ ↑Q ↔ h ∈ conjugate x ↑Q
  No goals
  ```

### `card_sylow_modEq_one`, lines 614–618

> **Theorem.** n_p ≡ 1 (mod p).

- **Line [616](Sylow.lean#L616), `obtain ⟨P, hP⟩ := exists_isSylowSubgroup (G := G) (p := p)`.**
  A Sylow subgroup P exists, by Sylow I.
- **Line [617](Sylow.lean#L617).** The counting congruence, for P acting on the
  Sylow subgroups:

  ```text
  this : Nat.card (SylowSet p G) ≡ Nat.card ↑(MulAction.fixedPoints (↥P) (SylowSet p G)) [MOD p]
  ```

- **Line [618](Sylow.lean#L618), `rwa [card_fixedPoints ⟨P, hP⟩] at this`.** The
  number of fixed points is 1. The result is the goal, because `numSylow p G`
  is `Nat.card (SylowSet p G)` by definition.

### `card_sylow_eq_index_normalizer`, lines 627–637

> **Theorem.** n_p = [G : N(P)].

- **Line [629](Sylow.lean#L629), `rw [← stabilizer_eq_normalizer, MulAction.index_stabilizer]`.**
  N(P) is the stabilizer of P (Stop 11), and orbit–stabilizer turns the index
  of the stabilizer into the size of the orbit. `Set.ncard` is the number of
  elements of a set. After each rule:

  ```text
  ⊢ numSylow p G = (MulAction.stabilizer G P).index
  ⊢ numSylow p G = (MulAction.orbit G P).ncard
  ```

- **Lines [631–635](Sylow.lean#L631-L635), `have horbit : MulAction.orbit G P = Set.univ`.**
  The orbit of P is everything (`Set.univ`). After `ext Q` and `simp only`, the
  goal is `Q ∈ MulAction.orbit G P`. Sylow II gives g with Q = gPg⁻¹, and
  `⟨g, …⟩` shows that Q = g • P:

  ```text
  g : G
  hg : ↑Q = conjugate g ↑P
  ⊢ Q ∈ MulAction.orbit G P
  ```

- **Lines [636–637](Sylow.lean#L636-L637), `rw [horbit, Set.ncard_univ]`, then `rfl`.**
  After each rule:

  ```text
  ⊢ numSylow p G = Set.univ.ncard
  ⊢ numSylow p G = Nat.card (SylowSet p G)
  ```

  The two sides are then equal by the definition of `numSylow`.

### `card_sylow_dvd`, lines 642–649

> **Theorem.** n_p divides m = |G|/p^n.

- **Line [645](Sylow.lean#L645), `rw [card_sylow_eq_index_normalizer ⟨P, hP⟩]`.**

  ```text
  ⊢ (Subgroup.normalizer ↑↑⟨P, hP⟩).index ∣ Nat.card G / p ^ (Nat.card G).factorization p
  ```

- **Lines [646–647](Sylow.lean#L646-L647), `have hidx : P.index = Nat.card G / p ^ …`.**
  By Lagrange, [G : P] = |G|/|P|. After each rule on line 647:

  ```text
  ⊢ P.index = Nat.card G / Nat.card ↥P
  ⊢ P.index = Nat.card ↥P * P.index / Nat.card ↥P
  No goals
  ```

  `Nat.mul_div_cancel_left` cancels |P| > 0.
- **Lines [648–649](Sylow.lean#L648-L649).** The goal becomes
  [G : N(P)] ∣ [G : P], which holds because P ≤ N(P)
  (`Subgroup.index_dvd_of_le`):

  ```text
  ⊢ (Subgroup.normalizer ↑↑⟨P, hP⟩).index ∣ P.index
  ```

## Stop 14. The statements of §1

**§6.6, lines [653–670](Sylow.lean#L653-L670).**

```lean
theorem sylowI (p : ℕ) (G : Type*) [Group G] : SylowI p G := fun _ hp =>
  haveI := Fact.mk hp
  exists_isSylowSubgroup
```

`SylowI p G` reads *if G is finite and p is prime, then …*, so, as in the
Lagrange file, its proof is a function of the two hypotheses. The difference is
that the lemmas take *p is prime* in square brackets, as `[Fact p.Prime]`, while
here it arrives as an ordinary hypothesis `hp`. `haveI := Fact.mk hp` converts
it, so that Lean can supply it to `exists_isSylowSubgroup` by itself. The
hypothesis `Finite G` needs no converting; the `_` leaves it unnamed.

`sylowII` and `sylowIII`, lines [664–670](Sylow.lean#L664-L670), work the same
way. In `sylowII`, the underscores of `fun _ hp _ _ hP hQ` leave unnamed the
finiteness of G and the subgroups P and Q, which the proof never mentions by
name. In `sylowIII`, the pair `⟨card_sylow_modEq_one, card_sylow_dvd⟩` proves
the two halves of the ∧.

## Stop 15. The checks at the end

**§7, lines [672–707](Sylow.lean#L672-L707).**

Lines [676–678](Sylow.lean#L676-L678) print the axioms that the three theorems
rest on. Each reports the standard three:

```text
'Projects.Example.sylowI' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An unfinished proof would add `sorryAx` to the list.

Lines [690–707](Sylow.lean#L690-L707) are a small program, not a proof. It
checks that the proofs never use Mathlib's own Sylow theorems, which would make
the exercise circular. Starting from the three theorems, it follows every name
each proof uses, then every name those use, and so on. It then lists the names
that come from `Mathlib/GroupTheory/Sylow.lean`. Click line
[691](Sylow.lean#L691) to see its report in the InfoView:

```text
12989 declarations checked; from Mathlib's Sylow file: []
```

The empty list `[]` means that there are none. The code is meta-programming,
which the seminar does not cover, so read it as a tool.

## Phrasebook additions

What this file uses beyond the
[phrasebook of `ReadingLagrange.md`](ReadingLagrange.md#phrasebook).

### Proof steps

| Lean | Read it as | First used |
|---|---|---|
| `obtain ⟨x, hx⟩ := e` | `e` says that some x exists: take one, call it `x`, and call its property `hx` | line [405](Sylow.lean#L405) |
| `rcases e with h \| ⟨⟨a, ha⟩⟩` | split the *or* `e` into two cases, unpacking each | line [289](Sylow.lean#L289) |
| `refine ⟨e, ?_⟩` | give part of a package now; each `?_` becomes a new goal | line [417](Sylow.lean#L417) |
| `set N := e` | like `let`, and also replaces `e` by `N` everywhere | line [375](Sylow.lean#L375) |
| `simpa [facts] using e` | simplify both `e` and the goal until they match | line [255](Sylow.lean#L255) |
| `rwa [e]` | `rw [e]`, then finish with a hypothesis | line [288](Sylow.lean#L288) |
| `calc` | a chain of equalities as on paper; `_` is the previous right side | line [464](Sylow.lean#L464) |
| `symm` | turn the goal a = b into b = a | line [601](Sylow.lean#L601) |
| `apply le_antisymm` | prove a = b as a ≤ b and b ≤ a | line [557](Sylow.lean#L557) |
| `\| 0, _ => …` and `\| k + 1, h => …` | a proof by induction, one line for each case | line [434](Sylow.lean#L434) |
| `haveI := Fact.mk hp` | make the hypothesis `hp` available in square brackets | line [661](Sylow.lean#L661) |
| `instance … where` | define something Lean supplies by itself, such as an action, part by part | line [517](Sylow.lean#L517) |

### Terms and notation

| Lean | Means | Type it as |
|---|---|---|
| `[Fact p.Prime]`, `hp.out` | *p is prime*, packaged for square brackets; `hp.out` takes the fact back out | |
| `G ⧸ H` | the left cosets of H; the quotient group when H is normal | `\quot` |
| `(x : G ⧸ H)`, shown as `↑x` | the coset xH | |
| `f ⁻¹' t` | the preimage of t under f | `\-1` then `'` |
| `g • x` | g acting on x | `\smul` |
| `MulAction.fixedPoints H X` | the points of X fixed by every element of H | |
| `MulAction.stabilizer G x`, `MulAction.orbit G x` | the stabilizer and the orbit of x | |
| `IsPGroup p H` | every element of H has order a power of p | |
| `H.index` | [G : H] | |
| `Subgroup.normalizer (H : Set G)` | N(H) | |
| `H.subgroupOf N` | H seen as a subgroup of N | |
| `K.map f`, `K.comap f` | the image and the preimage of a subgroup under f | |
| `N.subtype` | the inclusion of N in G | |
| `Subgroup.zpowers x` | the subgroup generated by x | |
| `⊥` | the trivial subgroup | `\bot` |
| `P ≤ Q` | P ⊆ Q, for subgroups | `\le` |
| `a ≡ b [MOD p]` | a ≡ b (mod p) | `\==` |
| `n.factorization p` | the exponent of p in n | |
| `A ∧ B` | A and B | `\and` |
| `P.1`, `P.2` | the two parts of a pair, such as a subgroup and the proof that it is Sylow | |
| `Subtype.ext` | two pairs are equal when their first parts are | |
| `h ▸ e` | `e`, rewritten with the equation `h` | `\t` |
| `(G := N ⧸ H')` | give the argument named `G` explicitly | |
| `congrArg f h` | from a = b, conclude f(a) = f(b) | |
| `?n` | in the InfoView, a placeholder that Lean fills in later | |
