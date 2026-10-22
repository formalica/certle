# Corner cases — `sign_proxy` / `scripts/SignProxy.lean`

This file records **every corner case** encountered while making
`lake exe sign_proxy --repo ./Mathlib/Algebra --in-place --axiom-module
Mathlib.SignedAxiom --axiom-name signedAxiom --no-axiom-file` produce *correct,
compiling* Lean files.

Every entry below cites the **original (unmodified, `HEAD`) Mathlib source file
and line number** — i.e. the location in Mathlib where that corner case actually
occurs. Line numbers were obtained with `git show HEAD:<path>`.

---

## 0. How the tool works (30 seconds)

1. Parse the file **parse-only** (no elaboration) with an environment that only
   contains `Batteries.Tactic.Lemma`. Loop `Parser.parseCommand` and collect the
   start byte of every command.
2. A declaration's *command span* is `[start of this command, start of the next
   standalone command)`.
3. Inside that span, a comment/string/bracket-aware **byte scanner**
   (`findBodyStart`) locates the proof-body separator: a depth-0 `:=`, an
   equation-style `| … =>`, or `where`.
4. `contentEnd` finds where that body stops; `applyEdits` splices
   `:= by sigSorry` over `[bodyStart, bodyEnd)`, back-to-front.
5. `public import Mathlib.SignedAxiom` is inserted after the last leading import.

`def` / `abbrev` / `instance` / `structure` / `inductive` are never touched.

---

# PART 1 — Corner cases found and handled

---

### CC-01 — Mathlib notation is unknown to the parse-only environment

**Original sites**

* `Mathlib/Algebra/Group/Hom/Basic.lean:250`
  `@[to_additive (attr := simp)] lemma mul_apply (f g : M →* N) (x : M) : …`
* `Mathlib/Algebra/Group/Semigroup.lean:70`
  `IsCancelMul R ↔ ∀ r : R, IsRegular r := by`
* Any declaration using `→+*`, `≫ₙ`, `⟶`, `≪`, `≃*`, … (thousands of them).

**What goes wrong**

`Lean.Parser.parseCommand` only has `Batteries.Tactic.Lemma` loaded, so `→+*`
etc. are *not* in the parser tables. Lean error-recovers by inserting `missing`
nodes and **never builds the `declVal` node**; the `declSig` is truncated.

The first prototype extracted the body range from `declVal`'s syntax range. With
no `declVal` node, `inner[getNumArgs - 1]` grabbed the *truncated `declSig`* and
the splice deleted the tail of the signature. **~7212 of ~23147 replacements were
corrupted** — this is the "95% of declarations mangled" report.

**Handling** — never trust syntax ranges for the body; locate the body with the
byte scanner (comment/string/bracket aware) instead.

---

### CC-02 — Corrupted output for `theorem` nodes with a `missing` keyword

**Original site** — any `@[attr] alias …` or unknown command (see CC-13).

**What goes wrong** — unknown commands are error-recovered as a
`Batteries.Tactic.Lemma.lemmaCmd` node whose leading atom is `missing`, so the
old code happily rewrote them.

**Handling** — `nodeKeyword` guard: only rewrite when the leading atom is
*literally* `theorem`, `example` or `lemma`.

---

### CC-03 — `|` absolute-value notation at the **start of a statement line**

**Original sites**

* `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:79`
  ```
  @[to_additive] lemma mabs_ite (p : Prop) [Decidable p] :
      |if p then a else b|ₘ = if p then |a|ₘ else |b|ₘ :=
    apply_ite _ _ _ _
  ```
* `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:83` (`mabs_dite`, same shape)
* `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:162`
  `|(a ⊔ c) / (b ⊔ c)|ₘ * … =` — the `:=` is on the **next** line
* `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:159, 187, 314`
* `Mathlib/Algebra/Order/Group/Abs.lean:38, 56, 111, 179, 184`

**What goes wrong**

The scanner used to treat *"first non-blank byte on its line"* + `|` as an
equation-style body start. That produced

```lean
@[to_additive] lemma mabs_ite (p : Prop) [Decidable p] :
    := by sigSorry        -- ← the whole statement was eaten
```

which fails with `unexpected token ':='; expected term`
(`Abs.lean:78, 81, 130, 140, 235` in the rewritten file).

**Handling** — a `|` counts as an equation body **only** if a depth-0 `=>`
follows it on the *same line*, and only **before** any depth-0 `:=`
(`pipeHasFatArrow`). None of the lines above contain a `=>`, so they now resolve
to the real `:=`.

---

### CC-04 — `|` at the start of a line that is a **tactic**, not an equation

**Original sites**

* `Mathlib/Algebra/Order/Interval/Basic.lean:543, 558`
  `        | cases h`
* `Mathlib/Algebra/Order/Interval/Basic.lean:544, 559`
  `        | congrm WithBot.some $(…)`
* `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:263`
  `        | pure none -- Fail if the body is not provably nonnegative`

**What goes wrong** — indented tactic lines beginning with `|` would be read as
the body start and everything before them would be deleted.

**Handling** — same rule as CC-03 (require a same-line, pre-`:=` `=>`). None of
these lines contain `=>`, so they are ignored. They are all *after* a real `:=`
anyway, so the real body separator is found first.

---

### CC-05 — `|>` (pipe operator) and other `|…` tokens at line start

**Original sites**

* `Mathlib/Algebra/Polynomial/Div.lean:464` — `|>.trans_le <| WithBot.coe_le_coe.mpr …`
* `Mathlib/Algebra/Module/LocalizedModule/Submodule.lean:244, 312` — `|>.restrictScalars _`
* `Mathlib/Algebra/Polynomial/Expand.lean:295` — `|>.mpr <| right_ne_zero_of_mul …`

**What goes wrong** — a leading `|` followed by `>` would otherwise look like an
equation pattern.

**Handling** — the scanner rejects `|` when the next byte is one of
`| > < -` (`nx != 0x7c/0x3e/0x3c/0x2d`), plus the `=>` requirement of CC-03.

---

### CC-06 — `rfl`-style proof bodies are **definitional**, not mathematical

**Original sites**

* `Mathlib/Algebra/Group/Hom/Basic.lean:250`
  `@[to_additive (attr := simp)] lemma mul_apply (f g : M →* N) (x : M) : (f * g) x = f x * g x := rfl`
* Whole-tree counts in `Mathlib/Algebra` (original): **2654** `:= rfl`,
  **106** `:= Iff.rfl`, **26** `:= by rfl`, **261** `| … => rfl`.

**What goes wrong** — if these are replaced by `:= by sigSorry` the *statement*
still type-checks, but the proof term is no longer a reflexive term.

**Handling** — `isReflBody` / `isReflTerm` recognise `rfl`, `by rfl`,
`by exact rfl`, `Iff.rfl`, `Eq.refl _`, `fun … => rfl`, `(rfl)` (after
whitespace normalisation) **and leave those bodies untouched**. This costs about
4966 replacements out of 28562 (~17%) but is mandatory for CC-07.

> **Why this is unavoidable:** `dsimp` (and `simp only` over definitional
> lemmas) only ever uses `[simp]` lemmas whose *proof* is a reflexive term — it
> rewrites by unfolding, not by applying the lemma's statement. Axiomatising
> them is therefore not sound w.r.t. the elaborator. See CC-07 for the concrete
> failure.

---

### CC-07 — `dsimp` inside an `instance` that depends on a `@[simp] rfl` lemma

**Original sites**

* `Mathlib/Algebra/GroupWithZero/Hom.lean:214`
  ```lean
  instance {β} [CommMonoidWithZero β] : Mul (α →*₀ β) where
    mul f g :=
      { (f * g : α →* β) with
        map_zero' := by dsimp; rw [map_zero, zero_mul] }   -- line 214
  ```
* it reduces via `Mathlib/Algebra/Group/Hom/Basic.lean:250` (`mul_apply := rfl`).

**What goes wrong** — with `mul_apply` axiomatised, the build fails with

```
error: Mathlib/Algebra/GroupWithZero/Hom.lean:214:22: `dsimp` made no progress
error: Mathlib/Algebra/GroupWithZero/Hom.lean:211:0: unknown free variable `_fvar.13200`
```

Reproduced in isolation:

```lean
import Mathlib.Algebra.Group.Hom.Basic
example (f g : M →* N) (x : M) : (f * g) x = f x * g x := by dsimp
--  -> `dsimp` made no progress     (fails when mul_apply := by sigSorry)
--  -> succeeds when mul_apply := rfl
```

Note the `instance`/`def` at line 214 is **identical** in old and new file — the
corruption is inherited from the *dependency*.

**Handling** — CC-06 (keep `rfl` bodies).

---

### CC-08 — `let … :=` inside the **statement**, not the body

**Original sites**

* `Mathlib/Algebra/Algebra/Epi.lean:79` — `let R' := (Algebra.linearMap R A).range`
* `Mathlib/Algebra/Algebra/Epi.lean:133` — `let f : M →ₗ[R] A ⊗[R] M :=`
* `Mathlib/Algebra/Algebra/Epi.lean:141` — `let f : A ⊗[R] A →ₗ[R] A ⊗[R] M := lift`
* `Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean:627` — `let S : NonUnitalSubalgebra R A :=`

**What goes wrong** — the first depth-0 `:=` in the span is the `let`'s, so the
body would start there and the `let` line plus everything up to it would be
deleted, i.e. part of the *statement* disappears.

**Handling** — `findBodyStart` tracks a `pendingBinder` flag: `let`, `letI`,
`have`, `haveI` set it, and the `:=` that immediately follows such a token is
skipped. Covered by self-test `T6` / `T6b`.

---

### CC-09 — `letI … :=` inside the statement

**Original sites**

* `Mathlib/Algebra/Group/Action/Hom.lean:61` — `letI : MulAction E G := MulAction.compHom _ f`
* `Mathlib/Algebra/Group/Action/Hom.lean:69` — same shape
* `Mathlib/Algebra/Group/Action/Hom.lean:79` — `[h : letI := compHom α f; IsPretransitive M α]`
* `Mathlib/Algebra/Group/TransferInstance.lean:50, 59, 69` — `letI := e.one` / `Equiv.mul e` / `Equiv.div e`

**What goes wrong** — same as CC-08; caused hard build failures in
`Group.Action.Hom` and `Group.TransferInstance`.

**Handling** — `letI` added to the binder-skip set (`let`, `letI`, `have`,
`haveI`).

---

### CC-10 — `have … :=` inside a *statement* region

**Original sites**

* `Mathlib/Algebra/AddConstMap/Basic.lean:272` — `have ha' : 0 ≤ a := ha.le`
* `Mathlib/Algebra/AffineMonoid/Irreducible.lean:99` — `have hr' : … := by`

**What goes wrong** — same class as CC-08/09 (though in practice these sit in
proofs, *after* the real `:=`, so they are usually reached only if the real
separator was missed).

**Handling** — `have` / `haveI` are in the binder-skip set as well.

---

### CC-11 — Equation-style (`| p => …`) proof bodies

**Original sites**

* `Mathlib/Algebra/AddConstMap/Basic.lean:209`
  `  | (n : ℕ) => by simp`
* `Mathlib/Algebra/AddConstMap/Basic.lean:210`
  `  | .negSucc n => by simp [← sub_eq_add_neg]`
* `Mathlib/Algebra/AddConstMap/Equiv.lean:45` — `  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl`
* Corpus: **2817** lines start with `|`, **2589** of them contain `=>`.

**What goes wrong** — there is no `:=` at all in these declarations, so a
`:=`-only scanner would find *nothing* (or worse, find a `:=` belonging to a
later tactic) and leave/steal the wrong bytes.

**Handling** — `findBodyStart` accepts a depth-0 `|` with a same-line `=>` as an
equation body start and marks it `eqStyle`. Also used by `isReflBody` for
`| … => rfl` (59 such bodies).

---

### CC-12 — `where` proof bodies

**Original sites**

* `Mathlib/Algebra/Algebra/Operations.lean:745`
  `theorem span_singleton_eq_one_iff {x : A} : span R {x} = 1 ↔ … where`
* `Mathlib/Algebra/Azumaya/Matrix.lean:65` — `theorem matrix [Nonempty n] : IsAzumaya R (Matrix n n R) where`
* `Mathlib/Algebra/BrauerGroup/Defs.lean:83` — `lemma is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where`

**What goes wrong** — no `:=` and no `|`; the whole `where` block is the body.

**Handling** — `where` is a body-start keyword (marked `eqStyle` so the `where`
token itself is replaced by `:= by sigSorry`). Self-test `T10`.

---

### CC-13 — `alias` (and other commands) are unknown to the parser environment

**Original sites**

* `Mathlib/Algebra/Algebra/Equiv.lean:179` — `  alias coe_ringEquiv_injective := toRingEquiv_injective`
* `Mathlib/Algebra/Algebra/Equiv.lean:284, 286`
* `Mathlib/Algebra/GradedFunLike.lean:67` — `alias ⟨Graded.mem_of_map_mem, Graded.map_mem_of_mem⟩ := Graded.map_mem_iff`

**What goes wrong**

`alias` comes from Mathlib, not from `Batteries.Tactic.Lemma`. The parser
error-recovers it as a `Batteries.Tactic.Lemma.lemmaCmd` node with a `missing`
keyword, and it reports **no range**. Two failure modes:

1. it gets *rewritten* like a lemma (its `:=` replaced), destroying the alias;
2. or it gets *swallowed* into the previous declaration's span, so the previous
   declaration's body range overruns into it.

**Handling**

* CC-02 (`nodeKeyword` must literally be `theorem`/`example`/`lemma`);
* a range-less command starting at column 0 still counts as a *standalone*
  command, so it bounds the previous declaration.

Self-test `T9`.

---

### CC-14 — Docstrings containing ```` ```lean ```` code blocks with fake theorems

**Original sites**

* `Mathlib/Algebra/Algebra/Defs.lean:48, 52, 60` — ```` ```lean ```` blocks inside
  `/-- … -/` module docs.

**What goes wrong** — a naive line/column scanner sees `theorem foo : … := …`
inside the docstring and rewrites documentation, or the code block's `:=`
confuses the body search.

**Handling** — the byte scanner skips block comments (`/- … -/`, including the
nested `/-- … -/`) and line comments before looking for tokens, and the parser
gives command spans, so a docstring stays inside the span of the declaration it
documents. Self-test `T8`.

---

### CC-15 — Column-0 continuation of a body vs. column-0 start of the next command

**Original sites**

*Continuation (must NOT end the body):*
* `Mathlib/Algebra/GroupWithZero/Defs.lean:179` — `{ IsLeftCancelMulZero.to_isRightCancelMulZero with }` (column 0, continuing the `:=` above)
* `Mathlib/Algebra/EuclideanDomain/Field.lean:26` — `{ toCommRing := toCommRing …` (column 0)
* `Mathlib/Algebra/Algebra/Unitization.lean:806` — `{ toFun := fun φ ↦ …` (column 0)
* `Mathlib/Algebra/Category/MonCat/FilteredColimits.lean:146` — `{ mul := fun x y => by …` (column 0)

*New declaration (must end the body):*
* `Mathlib/Algebra/GroupWithZero/Defs.lean:56` (`… :=`) followed by
  `Mathlib/Algebra/GroupWithZero/Defs.lean:62` (`lemma mul_right_inj' …`, column 0)
  and `Mathlib/Algebra/GroupWithZero/Defs.lean:64` (`end Mul`, column 0).

**What goes wrong** — "column 0 ⇒ new command" would truncate every
`{ … with }` body continuation; "column 0 never ends a body" would make the
body of one declaration swallow the next declaration.

**Handling** — `contentEnd` stops before a column-0 token **only if the previous
non-space byte `endsComplete`** (identifier char, `)`, `]`, `}`, `'`, `!`, `?`).
Operators and opening brackets do *not* count, so `{ … with }` continuations are
kept while `… rfl\nlemma next` terminates correctly.

---

### CC-16 — The parser splits a `by` block into indented "commands"

**Original sites** — any declaration with a tactic the parse env cannot parse,
e.g. `Mathlib/Algebra/Group/Semigroup.lean:70`,
`Mathlib/Algebra/Notation/Pi/Defs.lean`, `Mathlib/Algebra/Group/Conj.lean`
(reported as `unexpected token 'by'`, `unknown identifier '…'` on the rewritten
files).

**What goes wrong** — after the error the parser resyncs *inside* the proof and
may report extra commands. If those were treated as "next standalone command",
the declaration span would stop in the middle of its own proof, so
`contentEnd` would return early and the tail of the proof would leak out of the
declaration (this is exactly the failure in CC-20).

**Handling** — only *standalone* commands bound a declaration: a command that
either (a) the parser gave a range to, or (b) begins at column 0 after trivia.
Indented proof fragments do not bound. Self-test `T7` ("by-block fully
replaced", "orphan tactic gone").

---

### CC-17 — `@[to_additive (attr := simp)]` and other attribute payloads

**Original site** — `Mathlib/Algebra/Group/Hom/Basic.lean:250`,
`Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:63` (`@[to_additive]`), etc.

**What goes wrong** — attributes contain `(attr := simp)` with a `:=` inside
them; the body scanner must not stop there. Also `to_additive` *generates* the
additive twin from the body we just rewrote.

**Handling** — the scanner starts at the declaration node start, skips
`@[ … ]` as a bracket group (depth goes up and down), so the `:=` inside
attributes is never at depth 0. `to_additive` translating `by sigSorry`
elaborates fine (verified: `Mathlib.Algebra.Group.Hom.Basic` builds).

---

### CC-18 — `private` declarations

**Original site** — `Mathlib/Algebra/FreeAlgebra.lean:195`
`private theorem mk_mul (x y : Pre R X) : …`

**What goes wrong** — `--skip-private` must not rewrite them; by default they
*must* be rewritten.

**Handling** — `modsArePrivate` inspects the modifier node. The user's command
does not pass `--skip-private`, so the run reports `private skipped: 0`.

---

### CC-19 — `mutual … end`

**Original site** — **0 occurrences** in `Mathlib/Algebra` (verified with
`git grep -cE '^mutual$' HEAD -- 'Mathlib/Algebra/*.lean'`).

**Handling** — implemented anyway: `Parser.Command.mutual` is recursed into so
nested declarations are rewritten too.

---

### CC-20 — Trailing comments/blank lines must survive between declarations

**Handling** — `contentEnd` returns the end of the last *non-trivia* byte, so
trailing whitespace and comments stay in the file and still separate the
declarations. `insertImport` is idempotent and only inserts after the last
leading import.

---

### CC-21 — `set_option … in <declaration>` wraps the declaration in its own node

**Original sites** — **1677** occurrences of `^set_option … in$` in
`Mathlib/Algebra`, for example:

* `Mathlib/Algebra/Homology/Embedding/Connect.lean:112`
  ```lean
  111: set_option backward.isDefEq.respectTransparency false in
  112: @[reassoc (attr := simp)]
  113: lemma d_comp_d (n m p : ℤ) : h.d n m ≫ h.d m p = 0 := by
  ```
* `Mathlib/Algebra/Homology/Embedding/Connect.lean:97` → `lemma shape … := match n, m with`

**What goes wrong** — `Lean.Parser.Command.in` is declared as a
`trailing_parser` (`Lean/Parser/Command.lean:910 def «in» := trailing_parser`),
so `set_option … in` *and the whole following declaration* end up inside one
wrapper node. `collectEdits` only recognised `Parser.Command.declaration`,
`Batteries.Tactic.Lemma.lemmaCmd` and `Parser.Command.mutual`, so **every
wrapped declaration was silently skipped** (1677 `set_option … in` lines, i.e.
≈ 5.7 % of the 29 403 declarations in this corpus).

**Handling** — if the node kind is unrecognised, look for a
`declaration`/`lemmaCmd`/`mutual` node among its direct children and process
that with the same span. This recovered **891 replacements** (23 325 → 24 216)
and, in this very file, removed the last
`simp only [d]` failure described in CC-22.

---

### CC-22 — Axiomatising a proof can remove a *side effect* another tactic relied on

**Original sites**

* `Mathlib/Algebra/Homology/Embedding/Connect.lean:91`
  `@[simp] lemma d_negSucc (n m : ℕ) : h.d (.negSucc n) (.negSucc m) = K.d n m := by simp [d]`
* `Mathlib/Algebra/Homology/Embedding/Connect.lean:109` (the consumer)
  `    · simp only [d]` inside `lemma shape`

**What goes wrong** — elaborating `simp [d]` *generates and caches the
equational lemmas of the `def d`*. `d_negSucc` is rewritten to `:= by sigSorry`,
that side effect disappears, and the later `simp only [d]` (in a declaration
that was then still unrecognised, see CC-21) has nothing to rewrite:

```
error: Mathlib/Algebra/Homology/Embedding/Connect.lean:110:17: failed to generate equational theorem for `d`
error: Mathlib/Algebra/Homology/Embedding/Connect.lean:110:6: `simp` made no progress
```

Verified by restoring *only* that one line → the module builds again.

**Handling** — fixed by CC-21, not by keeping the proof: once
`set_option … in lemma shape` is recognised, `shape` itself is rewritten to
`:= by sigSorry`, so the dependent `simp only [d]` disappears entirely. Both
`d_negSucc` and `d_comp_d` are axiomatised.

---

# PART 2 — Corner cases deliberately SKIPPED

The following cases are *not* solved. When they are detected, the tool leaves
the declaration completely untouched (its original proof is preserved) instead
of risking a mangled file. A skipped declaration still compiles — it simply does
not get the axiom.

---

### SKIP-01 — `#adaptation_note /-- … -/` inside a proof body

**Original sites**

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:251`
  ```lean
  248: @[to_additive]
  249: lemma prod_fiberwise_eq_prod_filter (…) :
  250:     ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s with g i ∈ t, f i := by
  251:   rw [← prod_disjiUnion, disjiUnion_filter_eq]
  252:   #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  253:   intro x' hx y' hy hne
  ```
  (line numbers above are the *original*; `#adaptation_note` is on original
  line 252, the `rw` on 251)
* `Mathlib/Algebra/Category/Grp/FilteredColimits.lean:75-79`
  ```lean
  74: lemma colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
  75:     G.mk.{v, u} F ⟨j, x⟩ * … = G.mk F ⟨j, x * y⟩ := by
  76:   #adaptation_note /-- Prior to leanprover/lean4#12564, this was just
  77:   `simpa using colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)` -/
  78:   have := colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)
  79:   simpa using this
  ```

**Why it is hard** — `#adaptation_note` is a real command (both `: command`,
`: tactic` and `: term` variants exist, see `Mathlib/Tactic/AdaptationNote.lean:54-62`)
but the parse-only environment does not know it. Its **doc comment** is then
reported by the parser as the *start of a new command*, mid-line, in the middle
of the proof. The declaration span therefore ends right before ` /-- … -/`, so
`contentEnd` stops there, the `rw`/`#adaptation_note` bytes are eaten and the
remaining tactics leak out.

**Symptom in the rewritten file**

```lean
    ∏ j ∈ t, … , f i := by sigSorry /-- 2025-09-12 (kmill) … -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; …
```
```
error: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:203:157:
       unexpected identifier; expected 'lemma'
error: Mathlib/Algebra/Category/Grp/FilteredColimits.lean:75:66:
       unexpected token 'have'; expected 'lemma'
```

**Skip rule** — if the declaration span contains a `#`-prefixed token (a
`#command`) other than at the very start of the span, **do not rewrite** this
declaration.

**Refinement** — the first version of this rule used a bare `#`, which also
fired on the *cardinality notation* `#(range n)`, e.g.
`Mathlib/Algebra/Ring/GeomSum.lean:107` (`_ = #(range n) • x ^ (n - 1)`), and
skipped 342 declarations for no reason. It now requires `#` to be followed by an
identifier start (a letter or `_`), so `#adaptation_note`, `#guard_msgs`, … are
skipped while `#(…)` is not. **Current skip count: 181 declarations.**

---

### SKIP-02 — `:=` belonging to a nested `by` block inside the statement

**Original site**

* `Mathlib/Algebra/Category/Grp/EpiMono.lean:220-221`
  ```lean
  220: theorem g_apply_fromCoset (x : B) (y : X) :
  221:     g x (fromCoset y) = fromCoset ⟨x • ↑y,
  222:       by obtain ⟨z, hz⟩ := y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl
  ```

**Why it is hard** — the `:=` after `obtain ⟨z, hz⟩` is *not* the declaration's
body separator; it is a tactic binder inside a nested `by` that lives inside an
anonymous constructor `⟨ … ⟩` **in the statement**. Because `⟨ ⟩` are not bracket
tokens for the scanner, this `:=` is seen at depth 0 and everything up to it is
replaced.

**Symptom in the rewritten file**

```lean
theorem g_apply_fromCoset (x : B) (y : X) :
    g x (fromCoset y) = fromCoset ⟨x • ↑y,
      by obtain ⟨z, hz⟩ := by sigSorry

theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ := rfl
```
```
error: Mathlib/Algebra/Category/Grp/EpiMono.lean:191:38: unexpected token 'theorem'; expected '⟩'
error: Mathlib/Algebra/Category/Grp/EpiMono.lean:217:2: unknown metavariable '?_uniq.37020'
```

**Skip rule** — a *header balance check*: the text from the command start up to
the candidate body start must be bracket-balanced. If it still contains an
unclosed `⟨`, or the span contains a nested `by` before the candidate `:=`,
**do not rewrite** this declaration.

---

### SKIP-03 — Declaration spans that end in the middle of a proof

**Skip rule (general safety net)** — after computing `[bodyStart, bodyEnd)`:

* if the span `[start, nextStandalone)` contains a `#command` (SKIP-01),
* if the header `[start, bodyStart)` is not bracket-balanced (SKIP-02), or
* if `contentEnd` stopped at `end_` (the span boundary) rather than at a real
  column-0 boundary,

then the declaration is reported as `skipped-hard` and left byte-for-byte
unchanged. These are logged under the `SIGNPROXY_REPORT` dump with their line
number in the **original** input file, so they can be revisited later.

---

# PART 3 — Newly found / newly skipped corner cases (after the latest edit)

These were discovered while making the previous fixes and are recorded here at
the end of the file as requested.

---

### SKIP-04 — Spurious *mid-line* declaration nodes

**Original site**

* `Mathlib/Algebra/BigOperators/Finprod.lean:99`
  ```lean
  99: noncomputable irreducible_def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α → M) : M :=
 100:   if h : HasFiniteSupport (f ∘ PLift.down) then ∑ i ∈ h.toFinset, f i.down else 0
  ```
* `Mathlib/Algebra/BigOperators/Finprod.lean:106` — same shape for `finprod`

**Why it happens** — `irreducible_def` is not in the parse-only environment, so
the parser error-recovers and then re-lexes the *named argument* `lemma :=` of
`… finsum (lemma := finsum_def')` as a **`Batteries.Tactic.Lemma.lemmaCmd`**
whose range starts at that `lemma` — i.e. in the *middle of a line*, inside
parentheses. `collectEdits` saw `nodeKeyword == "lemma"` and rewrote it, giving

```lean
noncomputable irreducible_def finsum (lemma := by sigSorry
```
```
error: Mathlib/Algebra/BigOperators/Finprod.lean:100:46: unexpected token 'by'; expected identifier
error: Mathlib/Algebra/BigOperators/Finprod.lean:103:0: Unknown identifier `definition✝`
```

**Skip rule (new)** — a declaration is only processed when its parser range
**begins at column 0**. Real top-level declarations always do (doc comment,
attributes and modifiers included); fragments the parser splits out of a
declaration body never do. Commands rejected by this guard are simply left
unchanged (**~135 commands** in this corpus).

---

### SKIP-05 — Declaration spans bounded *inside* a proof

**Original sites** (same as SKIP-01)

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:251-253`
* `Mathlib/Algebra/Category/Grp/FilteredColimits.lean:75-79`

**Why it happens** — the *next standalone command* used to be defined as
"whatever the parser gave a range to". After an error inside a proof the parser
resyncs there and reports a range for a **doc comment glued to an embedded
`#adaptation_note`**, mid-line. The span therefore stopped in the middle of the
proof, `contentEnd` returned early, and the tail of the proof leaked out.

**Fix / skip rule (new)** — a command only bounds the previous declaration when
**its range (or, as a fallback, the position the parser was at before it) lies at
column 0**. Ranges are preferred because error recovery can make `state.pos`
overshoot past the start of the next command (using `state.pos` alone lost 327
replacements); column 0 is required because proof fragments and glued doc
comments are indented or mid-line.

---

### SKIP-06 — Unicode bracket imbalance ⇒ skip

**Original site**

* `Mathlib/Algebra/Category/Grp/EpiMono.lean:220-222` (same as SKIP-02)

**Rule (new)** — `findBodyStart` now balances `⟨ ⟩`, `⟦ ⟧`, `⟪ ⟫`, `⦃ ⦄` in
addition to `( ) [ ] { }`. A depth-0 `:=` is only accepted when *every* bracket
is closed, so:

* `… = fromCoset ⟨x • ↑y, by obtain ⟨z, hz⟩ := …⟩ := rfl` — the `obtain` `:=`
  sits at depth ≥ 1 and is no longer mistaken for the body separator (this
  *fixes* the declaration instead of skipping it);
* a statement with an irrecoverably unbalanced `⟨` yields `no-body-marker` and
  the declaration is **skipped**, left byte-for-byte unchanged.

---

## Final tally (Mathlib/Algebra, 1378 files, 29 403 declarations found)

| outcome | count | share |
|---|---:|---:|
| proof replaced by `:= by sigSorry` | **24 216** | **82.4 %** |
| kept — definitional `rfl` body (CC-06 / CC-07) | 4 993 | 17.0 % |
| skipped — `#command` inside the span (SKIP-01/04) | 194 | 0.7 % |

Of the **non-`rfl`** proof bodies, **99.2 %** are axiomatised (24 216 of
24 410). The `rfl` remainder is *mandatory*: see CC-06/CC-07 — removing those
proofs breaks `dsimp` everywhere in Mathlib.

Every non-replaced declaration is left **byte-identical** to the original, so
the file always still compiles; `SIGNPROXY_REPORT=1` prints every one of them
with its line number in the *input* file.
