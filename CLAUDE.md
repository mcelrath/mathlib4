# Mathlib4 fork — Claude working notes

This repo is a Mathlib4 fork used as the proof-engine for the
`secular-constraints` / `claude/proofs` framework. Some Phase C and
Hecke-FE work is being staged here as upstream-PR-clean material
(typically in `Mathlib/NumberTheory/NumberField/QuadraticField/`).

This CLAUDE.md is for the **fork branch `ag`** and should NOT be
included in any PR diff submitted to upstream Mathlib. Files
contributed upstream are individual `.lean` files; this `CLAUDE.md`
stays in the fork only.

---

## Non-trivial Lean proofs: use the trace_state debugger idiom

When writing any non-trivial Lean proof in this repo, use the
following pattern to turn `lake build` into a step-by-step debugger
equivalent to interactive Lean:

### 1. At the top of any new file or new section you're editing

```
set_option pp.coercions true
set_option pp.numericTypes true
```

Optionally, for typeclass-instance debugging:

```
set_option pp.all true
```

### 2. Between tactic steps in proofs you're actively writing

Sprinkle `trace_state` calls between each non-trivial tactic step.

Example:
```lean
theorem some_proof (x : Foo) : P x := by
  intro h
  trace_state
  rcases h with ⟨a, b, hab⟩
  trace_state
  apply some_lemma
  trace_state
  · exact hab.left
  · exact hab.right
```

### 3. Run `lake build` and read the log

Each `trace_state` checkpoint logs the full proof goal at that
position, including all casts and coercions (because of the
`pp.coercions` setting). This is **faster than the
edit-build-error-edit cycle** because you see goal state at every
intermediate step.

### 4. Before declaring done

**REMOVE** all `trace_state` calls. The `set_option pp.coercions`
and `set_option pp.numericTypes` lines at file top can stay — they
are cosmetic and useful for future readers.

### When this idiom is required

- Any proof that takes more than 5 build iterations to converge.
- Any proof involving coercion chains (`Nat.cast`, `Int.cast`,
  `algebraMap`, `Set.range`, `Finset.image`, etc.).
- Any `omega` or `nlinarith` invocation that fails inexplicably —
  trace_state right before it shows whether the hypotheses are
  in scope as expected.
- Any typeclass-heavy proof (instance synthesis surprises are
  diagnosed via `set_option pp.all true` at file top).

---

## Branch / commit hygiene

- Working branch: `ag`. Do NOT push to `master` or upstream.
- Each Phase C sub-task gets its own commit. See
  `~/.claude/plans/PLAN-phase-c-item-a-regulator-qsqrt3.md` for
  the 7-task DAG (T1-T7).
- Commit messages follow the upstream Mathlib pattern:
  `feat(NumberField): ...`, `feat(RingTheory): ...`, etc.
- Use `git commit --no-gpg-sign`. Do NOT skip hooks.

## Anti-patterns

- **Do NOT use `git checkout`** to revert uncommitted Lean drafts.
  The CLAUDE.md and dispatched agent prompts have documented multiple
  cases where this silently wiped predecessor work. If you need to
  revert a draft, use the Edit tool with `old_string`/`new_string`
  only, or `git restore --staged` for staged content.
- Do NOT modify existing Mathlib files outside the new file you're
  building. New work belongs in new files; cross-cutting upstream
  changes need separate planning.
- Do NOT add `axiom` or `sorry` to make a proof compile. Discharge
  or report obstruction.
- **Do NOT use `set_option maxHeartbeats 0`** in any file. This
  disables Lean's elaboration guard and lets `native_decide` runaways
  consume unbounded RAM (observed: 4 GB per `native_decide` branch on
  `Matrix (Fin 16) (Fin 16) ℚ` under v4.30, OOM-killed the host). Use
  `1600000` (2× default) if a single atomic call needs headroom.
- **Do NOT use `fin_cases i <;> fin_cases j <;> native_decide`** over
  `Matrix (Fin n) (Fin n) ℚ` for n ≥ 16. The branches accumulate
  elaboration state across cases. Split into separate top-level
  lemmas, or use the compute-in-Python / verify-once-in-Lean pattern
  (see secular-constraints `proofs/PerBlockChirality.lean::chi_B_involution`):
  prove minimal atoms (`R * Rᵀ = 1`, `R³ = 1`, `χ² = 1`) with one
  `native_decide` per equation; derive every downstream identity by
  `rw` / `Matrix.mul_assoc` / `Matrix.trace_mul_comm`. The native
  compiler is invoked only on atoms.

## Mathlib API quirks documented during this session

- `Pell.IsFundamental` contains a universal quantifier over an
  infinite type. `decide`/`native_decide` cannot discharge it.
  Use arithmetic-bound (`omega`) on the integer x — e.g., for
  d=3, fundamental solution (2,1) is proven via "no integer
  x with 1 < x < 2" via `omega`.
- `Zsqrtd d` has no `Algebra ℤ` / `IsIntegralClosure` instances
  for any d. These need to be provided by hand.
- `AdjoinRoot.lift`, `AdjoinRoot.powerBasis`, `pb.equivFun` are
  the canonical tools for working with adjunction-style number
  field constructions.
- `LSeries.term_of_ne_zero` produces `f n / (n:ℂ)^s` (note the
  divide) — use `norm_div`, NOT `norm_mul`, in summability bounds.
