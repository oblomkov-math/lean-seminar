# Reading `Lagrange.lean`

A guided walk through [`Lagrange.lean`](Lagrange.lean), to read next to VS Code.
Each stop gives the line numbers, says what the lines mean as mathematics, and
shows what the InfoView displays there. On GitHub, every line number below links
to that line of the file.

In VS Code:

- **Cmd+Shift+Enter** shows the InfoView.
- **Ctrl+G** jumps to a line number.
- Hover over a name to see its statement.
- **Cmd**-click a name to open where it is defined; **Ctrl+-** comes back.

The line numbers and the InfoView text below are taken from the file as it
compiles with Lean 4.34 and the seminar's Mathlib.

## Contents

- [The file at a glance](#the-file-at-a-glance)
- [How to read Lean](#how-to-read-lean)
- [Stop 1. The problem](#stop-1-the-problem), lines 29–43
- [Stop 2. The statement](#stop-2-the-statement), lines 45–73
- [Stop 3. The checks](#stop-3-the-checks), lines 75–121
- [Stop 4. The plan](#stop-4-the-plan), lines 123–143
- [Stop 5. Membership in a coset](#stop-5-membership-in-a-coset), lines 152–172
- [Stop 6. Cosets that meet are equal](#stop-6-cosets-that-meet-are-equal), lines 174–207
- [Stop 7. Each coset has |H| elements](#stop-7-each-coset-has-h-elements), lines 209–221
- [Stop 8. The count](#stop-8-the-count), lines 223–271
- [Stop 9. The theorem, and the example of §3](#stop-9-the-theorem-and-the-example-of-3), lines 275–292
- [Stop 10. The axiom check](#stop-10-the-axiom-check), lines 294–312
- [Phrasebook](#phrasebook)

## The file at a glance

The file follows the seminar's project template. Each bar shows where a part
sits among the 314 lines, to scale: one character is about five lines.

```text
Header and imports    1–27   ░░░░░·······················································
§0 The problem       29–43   ·····███····················································
§1 Statement         45–73   ········██████··············································
§2 Prerequisites     75–91   ··············▒▒▒···········································
§3 Vacuity guard     93–110  ··················▒▒▒·······································
§4 Junk values      112–121  ·····················▒▒·····································
§5 Proof route      123–143  ·······················████·································
§6 Proof            145–292  ····························████████████████████████████····
§7 Axiom check      294–312  ························································▒▒▒▒
```

█ the mathematics, to read first · ▒ the template's checks, to read once after
the proof · ░ setup

On a first pass, read §0, §1, §5 and §6. Inside §6, read each lemma's statement
before its proof. A statement says what is proved; the proof can wait until the
statements make sense.

## How to read Lean

### A statement, piece by piece

This is the lemma on lines [183–184](Lagrange.lean#L183-L184):

```lean
theorem coset_eq_of_mem {g x : G} {H : Subgroup G} (hx : x ∈ coset g H) :
    coset x H = coset g H := by
```

| Piece | Reads |
|---|---|
| `theorem coset_eq_of_mem` | *Lemma.* The name is how later proofs cite it. |
| `{g x : G} {H : Subgroup G}` | *Let g, x ∈ G, and let H be a subgroup of G.* |
| `(hx : x ∈ coset g H)` | *Suppose x ∈ gH.* `hx` is a label for this hypothesis, like (∗) in a paper. |
| `: coset x H = coset g H` | *Then xH = gH.* What follows the last colon is the claim. |
| `:= by` | *Proof.* The indented lines below it are the steps. |

Where is G? Line [150](Lagrange.lean#L150), `variable {G : Type*} [Group G]`,
says once for all of §6: *let G be a group.* Lean adds it to every lemma in the
section.

The three kinds of brackets tell you what happens when the lemma is used:

| Brackets | What they introduce | When you cite the lemma |
|---|---|---|
| `( )` | an argument or hypothesis that you supply | you write it: `card_coset g H` (line [248](Lagrange.lean#L248)) |
| `{ }` | an argument that Lean works out from the rest | you leave it out: `mem_coset` (line [171](Lagrange.lean#L171)) |
| `[ ]` | a standing assumption, such as *G is a group* or *G is finite* | Lean finds it by itself |

### The InfoView, line by line

Click at the end of a line inside a proof. The InfoView then shows the state of
the proof after that line. This is what it shows after line
[161](Lagrange.lean#L161):

```text
1 goal
case mp
G : Type u_1
inst✝ : Group G
g : G
H : Subgroup G
h : G
hh : h ∈ H
⊢ g⁻¹ * (g * h) ∈ H
```

- `case mp` names the part of the proof you are in: `mp` is the ⇒ half of an ↔,
  and `mpr` is the ⇐ half.
- The lines above `⊢` are what you know: the objects, and the hypotheses with
  their labels.
- `inst✝ : Group G` is the group structure on G. The mark ✝ means Lean chose
  the name, so you cannot refer to it.
- `h` and `hh` are new; line 161 introduced them.
- The line after `⊢` is the goal: what is left to prove.
- When a part of the proof is finished, the InfoView says *No goals*.

Below, the InfoView blocks show only the lines that change, and the goal. The
full picture is always in VS Code.

## Stop 1. The problem

**§0, lines [29–43](Lagrange.lean#L29-L43).** The theorem as a textbook states
it: for a subgroup H of a finite group G, |G| = |H| · [G : H], so |H| divides
|G|.

Below it, the file records two decisions that the textbook leaves implicit. A
coset is a set, gH = {gh | h ∈ H}. The index [G : H] counts distinct cosets, so
it is the size of a set whose elements are themselves sets.

## Stop 2. The statement

**§1, lines [45–73](Lagrange.lean#L45-L73).** Three definitions supply the
vocabulary, and a fourth states the theorem. Each one in Lean, then in ordinary
notation:

```lean
def coset {G : Type*} [Group G] (g : G) (H : Subgroup G) : Set G :=
  {x | ∃ h ∈ H, g * h = x}
```

Line [56](Lagrange.lean#L56). gH = {x | x = gh for some h ∈ H}. The type after
the colon, `Set G`, says that the result is a subset of G.

```lean
def cosets {G : Type*} [Group G] (H : Subgroup G) : Set (Set G) :=
  {C | ∃ g : G, C = coset g H}
```

Line [60](Lagrange.lean#L60). The set of all left cosets, {gH | g ∈ G}. Its
type, `Set (Set G)`, says that it is a set of subsets of G.

```lean
noncomputable def numCosets {G : Type*} [Group G] (H : Subgroup G) : ℕ :=
  Nat.card (cosets H)
```

Line [67](Lagrange.lean#L67). [G : H], the number of cosets. `Nat.card` counts
the elements of a set. The word `noncomputable` only tells Lean not to try to
evaluate it; proofs are unaffected.

```lean
def Lagrange (G : Type*) [Group G] : Prop :=
  Finite G → ∀ H : Subgroup G, Nat.card G = Nat.card H * numCosets H
```

Line [72](Lagrange.lean#L72). *If G is finite, then |G| = |H| · [G : H] for
every subgroup H.* Read the arrow → as *implies*.

This last one is a definition of type `Prop`: it names the statement without
proving it. Lean reads a file from top to bottom, and the lemmas the proof needs
come later, in §6. So the theorem itself, `lagrange : Lagrange G`, is proved at
line [281](Lagrange.lean#L281).

## Stop 3. The checks

**§2–§4, lines [75–121](Lagrange.lean#L75-L121).** These three sections are the
template's safeguards. They make sure the statement means what it should. Skim
them now, and read them properly after the proof.

- **§2, lines [75–91](Lagrange.lean#L75-L91).** Each `#check` line pairs an
  object of the statement with Mathlib's declaration. Click one to see the
  declaration in the InfoView. Line [88](Lagrange.lean#L88) confirms that
  `coset g H` is Mathlib's own coset `g • H`. Its proof is `rfl`, which means
  the two agree by definition.
- **§3, lines [93–110](Lagrange.lean#L93-L110).** The hypotheses can be met: S₃
  is finite, with the subgroup A₃. Lines [105–110](Lagrange.lean#L105-L110)
  compute |S₃| = 6 and |A₃| = 3, which §6 uses at the end.
- **§4, lines [112–121](Lagrange.lean#L112-L121).** Lean sets `Nat.card` of an
  infinite set to 0, a meaningless value. That is why the statement assumes
  `Finite G`.

## Stop 4. The plan

**§5, lines [123–143](Lagrange.lean#L123-L143).** Read §5 closely before §6. It
is the proof in words, and §6 follows it step by step.

> **The proof on paper**
>
> 1. x ∈ gH exactly when g⁻¹x ∈ H. In particular g ∈ gH.
>    ([Stop 5](#stop-5-membership-in-a-coset))
> 2. If x ∈ gH, then xH = gH. ([Stop 6](#stop-6-cosets-that-meet-are-equal))
> 3. |gH| = |H|, because h ↦ gh is injective.
>    ([Stop 7](#stop-7-each-coset-has-h-elements))
> 4. Sort the elements of G by their coset. The elements with coset gH are those
>    of gH, and there are |H| of them, so |G| is a sum of [G : H] terms, each
>    equal to |H|. ([Stop 8](#stop-8-the-count))

The `#check` lines at the end of §5 list four general facts about counting that
the proof takes from Mathlib. Apart from these, it uses only the axioms of
groups and subgroups, such as a⁻¹(ab) = b and the closure of H under
multiplication.

## Stop 5. Membership in a coset

**§6.1, lines [152–172](Lagrange.lean#L152-L172).**

> **Lemma.** x ∈ gH ⟺ g⁻¹x ∈ H.
>
> **Proof.** If x = gh with h ∈ H, then g⁻¹x = h ∈ H. Conversely, if g⁻¹x ∈ H,
> take h = g⁻¹x; then gh = x.

### `mem_coset`

- **Line [158](Lagrange.lean#L158), the statement.** It has no hypotheses in
  round brackets, and the claim is an ↔.

  ```lean
  theorem mem_coset {g x : G} {H : Subgroup G} : x ∈ coset g H ↔ g⁻¹ * x ∈ H := by
  ```

  ```text
  ⊢ x ∈ coset g H ↔ g⁻¹ * x ∈ H
  ```

- **Line [159](Lagrange.lean#L159), `constructor`.** Prove the ↔ as two
  implications. Lean now has two goals: `mp` for ⇒ and `mpr` for ⇐.

  ```text
  2 goals
  case mp
  ⊢ x ∈ coset g H → g⁻¹ * x ∈ H

  case mpr
  ⊢ g⁻¹ * x ∈ H → x ∈ coset g H
  ```

- **Line [161](Lagrange.lean#L161), `rintro ⟨h, hh, rfl⟩`.** The bullet `·` on
  line 160 starts the first goal. Assume x ∈ gH, which says
  `∃ h ∈ H, g * h = x`, and unpack it: name the element `h` and the fact
  `hh : h ∈ H`. The last pattern, `rfl`, uses the equation `g * h = x` to
  replace x by `g * h` everywhere. That is why x disappears.

  ```text
  h : G
  hh : h ∈ H
  ⊢ g⁻¹ * (g * h) ∈ H
  ```

- **Line [163](Lagrange.lean#L163), `rw [inv_mul_cancel_left]`.** Rewrite with a
  group law from Mathlib, `inv_mul_cancel_left : a⁻¹ * (a * b) = b`. Hover over
  the name to see it.

  ```text
  ⊢ h ∈ H
  ```

- **Line [164](Lagrange.lean#L164), `exact hh`.** The goal is exactly the
  hypothesis `hh`. The first goal is done, and the second, `mpr`, comes next.

- **Line [166](Lagrange.lean#L166), `intro hx`.** The second bullet, on line 165,
  starts the ⇐ direction. Assume g⁻¹x ∈ H, and call it `hx`.

  ```text
  case mpr
  hx : g⁻¹ * x ∈ H
  ⊢ x ∈ coset g H
  ```

- **Line [167](Lagrange.lean#L167), `exact ⟨g⁻¹ * x, hx, mul_inv_cancel_left g x⟩`.**
  The goal says `∃ h ∈ H, g * h = x`. Prove it by giving three things in angle
  brackets: the element `g⁻¹ * x`, the proof `hx` that it lies in H, and the
  equation `g * (g⁻¹ * x) = x`, which is Mathlib's `mul_inv_cancel_left`.
  *No goals.*

> [!TIP]
> **Try it.** Delete line 164, `exact hh`. A red underline appears at the bullet
> on line 160, and the message reads *unsolved goals*, ending with `⊢ h ∈ H`.
> That is the goal you left open. Press Cmd+Z to put the line back.

### `mem_coset_self`

Every element lies in its own coset, g ∈ gH, because g⁻¹g = 1 ∈ H.

- **Line [171](Lagrange.lean#L171), `rw [mem_coset, inv_mul_cancel]`.** Two
  rewrites in a row: first the lemma just proved, then the group law
  `inv_mul_cancel : a⁻¹ * a = 1`. To see the goal between the two, put the
  cursor just after the comma. Before, between and after:

  ```text
  ⊢ g ∈ coset g H
  ⊢ g⁻¹ * g ∈ H
  ⊢ 1 ∈ H
  ```

- **Line [172](Lagrange.lean#L172), `exact H.one_mem`.** A subgroup contains 1.
  `H.one_mem` is short for `Subgroup.one_mem H`: when `H` is a subgroup, Lean
  reads `H.name` as the lemma `Subgroup.name` applied to `H`. *No goals.*

## Stop 6. Cosets that meet are equal

**§6.2, lines [174–207](Lagrange.lean#L174-L207).**

> **Lemma.** If x ∈ gH, then xH = gH.
>
> **Proof.** We know g⁻¹x ∈ H. Let y ∈ G. If x⁻¹y ∈ H, then
> g⁻¹y = (g⁻¹x)(x⁻¹y) ∈ H. If g⁻¹y ∈ H, then x⁻¹y = (g⁻¹x)⁻¹(g⁻¹y) ∈ H. By
> the first lemma, y ∈ xH ⟺ y ∈ gH.

### `coset_eq_of_mem`

- **Lines [183–184](Lagrange.lean#L183-L184), the statement.** It is the one
  taken apart in [How to read Lean](#how-to-read-lean).

  ```text
  hx : x ∈ coset g H
  ⊢ coset x H = coset g H
  ```

- **Line [185](Lagrange.lean#L185), `rw [mem_coset] at hx`.** With `at hx`, the
  rewrite acts on the hypothesis `hx` instead of the goal.

  ```text
  hx : g⁻¹ * x ∈ H
  ⊢ coset x H = coset g H
  ```

- **Line [186](Lagrange.lean#L186), `ext y`.** Two sets are equal when they have
  the same elements. Take any `y`.

  ```text
  y : G
  ⊢ y ∈ coset x H ↔ y ∈ coset g H
  ```

- **Line [187](Lagrange.lean#L187), `rw [mem_coset, mem_coset]`.** The first
  lemma, once for each side.

  ```text
  ⊢ x⁻¹ * y ∈ H ↔ g⁻¹ * y ∈ H
  ```

- **Lines [188–190](Lagrange.lean#L188-L190), `constructor`, then `intro hy`.**
  Two directions again. In the first, assume x⁻¹y ∈ H.

  ```text
  case mp
  hy : x⁻¹ * y ∈ H
  ⊢ g⁻¹ * y ∈ H
  ```

- **Line [191](Lagrange.lean#L191), `have e : g⁻¹ * y = (g⁻¹ * x) * (x⁻¹ * y) := by group`.**
  A side fact, named `e` and proved on the spot. The `group` tactic proves any
  equation that holds in every group. The InfoView drops the first pair of
  brackets: Lean reads `a * b * c` as `(a * b) * c`.

  ```text
  e : g⁻¹ * y = g⁻¹ * x * (x⁻¹ * y)
  ⊢ g⁻¹ * y ∈ H
  ```

- **Line [192](Lagrange.lean#L192), `rw [e]`.** Replace `g⁻¹ * y` by the
  product.

  ```text
  ⊢ g⁻¹ * x * (x⁻¹ * y) ∈ H
  ```

- **Line [193](Lagrange.lean#L193), `exact H.mul_mem hx hy`.** H is closed under
  multiplication, and the two factors lie in H by `hx` and `hy`. The second
  direction, `mpr`, comes next.

- **Lines [194–198](Lagrange.lean#L194-L198), the other direction.** It goes the
  same way, with `e : x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y)`. `H.inv_mem hx` says
  that (g⁻¹x)⁻¹ ∈ H, because H is closed under inverses. Before the last line:

  ```text
  hy : g⁻¹ * y ∈ H
  ⊢ (g⁻¹ * x)⁻¹ * (g⁻¹ * y) ∈ H
  ```

> [!TIP]
> **Try it.** On line 187, put the cursor just after the first `mem_coset,`. The
> InfoView shows the goal halfway through, `x⁻¹ * y ∈ H ↔ y ∈ coset g H`. Only
> the left side has been rewritten so far.

### `coset_eq_iff`

Lines [202–207](Lagrange.lean#L202-L207) combine the two lemmas:
xH = gH ⟺ x ∈ gH.

- **Lines [203–204](Lagrange.lean#L203-L204), `constructor`, then `intro h`.**
  For ⇒, assume xH = gH.

  ```text
  h : coset x H = coset g H
  ⊢ x ∈ coset g H
  ```

- **Line [205](Lagrange.lean#L205), `rw [← h]`.** The arrow ← makes the rewrite
  go from right to left: `coset g H` becomes `coset x H`. Type the arrow as
  `\l`.

  ```text
  ⊢ x ∈ coset x H
  ```

- **Lines [206–207](Lagrange.lean#L206-L207).** The goal is `mem_coset_self`
  from Stop 5. The ⇐ direction is exactly the lemma just proved; Lean fills in
  `g`, `x` and `H` by itself. *No goals.*

## Stop 7. Each coset has |H| elements

**§6.3, lines [209–221](Lagrange.lean#L209-L221).**

> **Lemma.** |gH| = |H|.
>
> **Proof.** gH is the image of H under h ↦ gh, which is injective.

```lean
theorem card_coset (g : G) (H : Subgroup G) : Nat.card (coset g H) = Nat.card H :=
  Nat.card_image_of_injective (mul_right_injective g) H
```

This proof has no `by` and no steps. It is a single expression: a Mathlib
theorem applied to two arguments. Read it as a citation. *By
`Nat.card_image_of_injective`, applied to the injective map h ↦ gh and to the
set H.*

`Nat.card_image_of_injective` says that if f is injective, then
`Nat.card (f '' s) = Nat.card s` for every set s. Here `f '' s` is Mathlib's
notation for the image f(s). `mul_right_injective g` is the fact that h ↦ gh is
injective.

The theorem applies directly because Mathlib defines the image `f '' s` as
`{x | ∃ a ∈ s, f a = x}`. That has the same form as our `coset` on line
[57](Lagrange.lean#L57).

> [!TIP]
> **Try it.** Hover over `Nat.card_image_of_injective` on line 221 to read its
> statement. Then Cmd-click `coset` on line 220 to jump to its definition, and
> press Ctrl+- to come back.

## Stop 8. The count

**§6.4, lines [223–271](Lagrange.lean#L223-L271).**

> **Theorem.** |G| = |H| · [G : H].
>
> **Proof.** Let f(x) = xH. *Step 1:* sorting G by cosets, |G| is the sum, over
> the cosets C, of the number of x with f(x) = C. *Step 2:* for C = gH, the x
> with xH = gH are the elements of gH, so each term is |H|. *Step 3:* a sum of
> [G : H] terms equal to |H| is |H| · [G : H].

This is the longest proof in the file, at lines
[236–264](Lagrange.lean#L236-L264). Most of its length is bookkeeping about how
Lean counts.

### Setting up, lines 239–240

- **Line [239](Lagrange.lean#L239), `have := Fintype.ofFinite (cosets H)`.**
  Bookkeeping. To write a sum over all cosets, Lean wants the set of cosets as
  an explicit finite list, and this line supplies one. It carries no
  mathematics.

  ```text
  this : Fintype ↑(cosets H)
  ```

- **Line [240](Lagrange.lean#L240), `let f : G → cosets H := fun x => ⟨coset x H, x, rfl⟩`.**
  The map f(x) = xH. An element of `cosets H` is a set packaged with a proof
  that it is a coset. Here the proof is `x, rfl`: xH is the coset of x, by
  definition.

  ```text
  f : G → ↑(cosets H) := fun x => ⟨coset x H, ⋯⟩
  ```

The InfoView hides proofs as `⋯`. An arrow such as `↑` or `↥` marks a set or
subgroup used as a type of elements, which is what `Nat.card` counts. Lean
inserts these arrows by itself.

### Step 1, lines 242–243: sort the elements by coset

```lean
have step1 : Nat.card G = ∑ C : cosets H, Nat.card {x // f x = C} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
```

`{x // f x = C}` is the set of x with f(x) = C, as a type, so that it can be
counted. `Equiv.sigmaFiberEquiv f` is the bijection between G and the pairs
(C, x) with f(x) = C. `Nat.card_congr` turns a bijection into equal counts, and
`Nat.card_sigma` counts the pairs class by class, as a sum. After the first
rewrite on line [243](Lagrange.lean#L243), the InfoView shows the pairs:

```text
⊢ Nat.card ((y : ↑(cosets H)) × { x // f x = y }) = ∑ C, Nat.card { x // f x = C }
```

### Step 2, lines 245–258: each term is |H|

- **Line [247](Lagrange.lean#L247), `rintro ⟨_, g, rfl⟩`.** Let C be a coset, so
  C = gH for some g. As on line 161, `rfl` substitutes gH for C.

  ```text
  g : G
  ⊢ Nat.card { x // f x = ⟨coset g H, ⋯⟩ } = Nat.card ↥H
  ```

- **Line [248](Lagrange.lean#L248), `rw [← card_coset g H]`.** Replace |H| by
  |gH|, using Stop 7 from right to left.

  ```text
  ⊢ Nat.card { x // f x = ⟨coset g H, ⋯⟩ } = Nat.card ↑(coset g H)
  ```

- **Line [251](Lagrange.lean#L251), `apply Nat.card_congr`.** Two sets have the
  same size when there is a bijection between them, so it suffices to give one.
  The symbol `≃` means *a bijection between*.

  ```text
  ⊢ { x // f x = ⟨coset g H, ⋯⟩ } ≃ ↑(coset g H)
  ```

- **Lines [252–253](Lagrange.lean#L252-L253), `apply Equiv.subtypeEquivRight`,
  then `intro x`.** Both sides are sets of elements of G, each cut out by a
  condition. If the two conditions are equivalent, the sets are the same, and
  the identity is a bijection. After line 252:

  ```text
  ⊢ ∀ (x : G), f x = ⟨coset g H, ⋯⟩ ↔ x ∈ coset g H
  ```

- **Line [256](Lagrange.lean#L256), `rw [Subtype.ext_iff]`.** `f x` and
  `⟨coset g H, ⋯⟩` are packages, each a set with a proof. Two packages are equal
  when the sets inside them are equal.

  ```text
  ⊢ ↑(f x) = ↑⟨coset g H, ⋯⟩ ↔ x ∈ coset g H
  ```

- **Line [257](Lagrange.lean#L257), `show coset x H = coset g H ↔ x ∈ coset g H`.**
  `show` restates the goal in a plainer form. Lean accepts it only if the new
  form means the same thing by definition.

  ```text
  ⊢ coset x H = coset g H ↔ x ∈ coset g H
  ```

- **Line [258](Lagrange.lean#L258), `exact coset_eq_iff`.** This is the lemma
  from Stop 6. Step 2 is done.

### Step 3, lines 260–264: add up

- **Line [260](Lagrange.lean#L260), `rw [step1, Finset.sum_const_nat fun C _ => step2 C]`.**
  Replace |G| by the sum from step 1. Then `Finset.sum_const_nat`, with step 2
  as its input, turns a sum of equal terms into a product. `Finset.univ.card`
  is the number of terms, that is, the number of cosets.

  ```text
  ⊢ Finset.univ.card * Nat.card ↥H = Nat.card ↥H * numCosets H
  ```

- **Line [264](Lagrange.lean#L264), `rw [Finset.card_univ, ← Nat.card_eq_fintype_card, numCosets, mul_comm]`.**
  Bookkeeping. `Finset.univ.card`, `Fintype.card` and `Nat.card` are three of
  Lean's ways to count the same finite set. The first two rules convert one
  into the next. Then `numCosets` unfolds the definition, and `mul_comm` swaps
  the two factors. After each rule:

  ```text
  ⊢ Fintype.card ↑(cosets H) * Nat.card ↥H = Nat.card ↥H * numCosets H
  ⊢ Nat.card ↑(cosets H) * Nat.card ↥H = Nat.card ↥H * numCosets H
  ⊢ Nat.card ↑(cosets H) * Nat.card ↥H = Nat.card ↥H * Nat.card ↑(cosets H)
  No goals
  ```

### The corollary, lines 270–271

```lean
theorem card_subgroup_dvd [Finite G] (H : Subgroup G) : Nat.card H ∣ Nat.card G :=
  ⟨numCosets H, card_eq_card_mul_numCosets H⟩
```

In Lean, `a ∣ b` is defined to mean that b = a · c for some c. A proof of an
existence statement is a package: the witness and the proof about it. Here the
witness is [G : H], and the proof is the formula just proved.

The divides sign `∣` is a different character from the keyboard's `|`. Type it
as `\|` or `\dvd`.

## Stop 9. The theorem, and the example of §3

**§6.5–§6.6, lines [275–292](Lagrange.lean#L275-L292).**

```lean
theorem lagrange (G : Type*) [Group G] : Lagrange G := fun _ H =>
  card_eq_card_mul_numCosets H
```

Lines [281–282](Lagrange.lean#L281-L282) prove the statement of §1.
`Lagrange G` has the form *if G is finite, then for every H, …*. A proof of
such a statement is a function. It takes a proof that G is finite and a
subgroup H, and returns a proof of the formula for that H. `fun _ H => …` is
that function.

The underscore stands for the proof that G is finite. It needs no name, because
the formula takes `[Finite G]` in square brackets, and Lean finds it there by
itself.

### Back to S₃, lines 288–292

§3 predicted [S₃ : A₃] = 2. Here the formula confirms it.

- **Line [289](Lagrange.lean#L289), `have h := card_eq_card_mul_numCosets (alternatingGroup (Fin 3))`.**
  Apply the formula to A₃ inside S₃, and call the result `h`.

  ```text
  h : Nat.card (Equiv.Perm (Fin 3)) = Nat.card ↥(alternatingGroup (Fin 3)) * numCosets (alternatingGroup (Fin 3))
  ⊢ numCosets (alternatingGroup (Fin 3)) = 2
  ```

- **Line [290](Lagrange.lean#L290), `rw [card_S₃, card_A₃] at h`.** Put in
  |S₃| = 6 and |A₃| = 3 from §3.

  ```text
  h : 6 = 3 * numCosets (alternatingGroup (Fin 3))
  ⊢ numCosets (alternatingGroup (Fin 3)) = 2
  ```

- **Line [292](Lagrange.lean#L292), `omega`.** `omega` solves linear equations
  and inequalities over ℕ and ℤ. Here it solves 6 = 3n. *No goals.*

## Stop 10. The axiom check

**§7, lines [294–312](Lagrange.lean#L294-L312).** Click line
[298](Lagrange.lean#L298), `#print axioms lagrange`. The InfoView lists the
axioms that the proof rests on:

```text
'Projects.Example.lagrange' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are the standard axioms that all of Mathlib uses. An unfinished
proof would add `sorryAx` to the list.

Lines [307–312](Lagrange.lean#L307-L312) check our count against Mathlib's.
Mathlib counts cosets its own way, through the quotient G/H, and calls the
count `H.index`. Both formulas hold, so |H| · `H.index` = |H| · `numCosets H`,
and cancelling |H| > 0 gives `numCosets H = H.index`.

The proof also avoids Mathlib's own theory of cosets. Following every name it
uses, 7,273 declarations in all, none comes from Mathlib's files on cosets,
indices or quotient groups. §7 of [`Sylow.lean`](Sylow.lean) shows how to run
such a check.

## Phrasebook

Every proof step and symbol used in this file, with how to read it.

### Proof steps

| Lean | Read it as |
|---|---|
| `constructor` | To prove A ↔ B, prove A → B and B → A. The two goals are called `mp` and `mpr`. |
| `·` | Work on the next goal. Type it as `\.` |
| `intro h` | Assume the hypothesis and call it `h`. For a ∀, *let h be arbitrary*. |
| `rintro ⟨h, hh, rfl⟩` | Assume, and unpack an ∃ at once. `rfl` substitutes, using the equation it receives. |
| `rw [e]` | Rewrite the goal with the equation or ↔ `e`, left side to right side. `rw [← e]` goes right to left; `rw [e] at h` rewrites the hypothesis `h`. |
| `exact t` | `t` proves the goal as it stands. |
| `apply t` | `t` would prove the goal, given its hypotheses; prove those next. |
| `ext y` | Two sets are equal when they have the same elements: take any `y`. |
| `have e : P := …` | A side fact `P`, proved on the spot and called `e`. |
| `let f := …` | A local definition: `f` names the expression. |
| `show P` | Restate the goal as `P`, which must mean the same by definition. |
| `group` | Prove an equation that holds in every group. |
| `simp` | Simplify, with Mathlib's standard list of rewriting rules. |
| `decide` | Settle a finite question by computation. |
| `omega` | Linear arithmetic over ℕ and ℤ. |
| `rfl` | True by definition. |

### Symbols and notation

| Lean | Means | Type it as |
|---|---|---|
| `Nat.card S` | the number of elements of S; 0 if S is infinite | |
| `{x \| P x}` | the set of x such that P(x) | |
| `{x // P x}` | the same set, used as a type, so its elements can be counted | |
| `↥H`, `↑S` | a subgroup or set used as a type of elements; Lean inserts the arrow | |
| `∃ h ∈ H, P h` | there is h ∈ H with P(h) | `\ex`, `\in` |
| `∀`, `→`, `↔`, `←` | for all, implies, if and only if, the reverse arrow in `rw` | `\all`, `\to`, `\iff`, `\l` |
| `⟨a, b, c⟩` | a package: a witness with the proofs about it | `\<`, `\>` |
| `g⁻¹` | the inverse of g | `\-1` |
| `a ∣ b` | a divides b | `\dvd` |
| `∑ C, …` | the sum over all C | `\sum` |
| `A ≃ B` | a bijection between A and B | `\equiv` |
| `fun x => …` | the function x ↦ … | |
| `⊢` | in the InfoView: the goal follows | |
| `inst✝`, `⋯` | in the InfoView: an unnamed assumption; a hidden proof | |

When this file reads easily, [`Sylow.lean`](Sylow.lean) in the same folder is
the next step. It uses the same moves on a larger scale.
