# UFRF – No Free Parameters at the Monster Scale

**Author:** Daniel Charboneau

This document explains how the repo formalizes the claim that the UFRF parameters at the Monster scale are uniquely determined by the axioms – there are **no tunable knobs**.

## 1. Global Parameter Structure

`lean/UFRF/Params.lean` defines:

- `structure UFRF.Params` with fields:
  - `phi : ℝ` – golden ratio;
  - `cycleLen : ℕ` – harmonic cycle length (13);
  - `restPhase : ℕ` – REST / E=B balance position.

- Axioms:
  - `phi_golden : phi^2 = phi + 1`  
  - `phi_gt_one : 1 < phi`  
  - `cycleLen_13 : cycleLen = 13`  
  - `restPhase_lt : restPhase < cycleLen`  
  - `restPhase_rest : isREST restPhase`  

Here `isREST` is a predicate defined via the **breathing amplitude**.

## 2. Breathing Amplitude and REST

We define a breathing amplitude function `breathingAmp (i : ℕ) : ℝ`
on positions `i = 0,…,12`, symmetric about the midpoint `6.5`. Let:

- `seedPhase : ℕ := 3`
- `mid : ℝ := 6.5`

Then:

- `breathingAmp 3 = 6/13`
- For positions `i ≤ 6`, `breathingAmp i = i / 6.5`
- For positions `i > 6`, `breathingAmp i = (13 - i) / 6.5`

We say:

```lean
isREST (i : ℕ) : Prop :=
  i > 6 ∧ breathingAmp i = breathingAmp seedPhase
```

This encodes:

> REST is the unique position on the "upper" side of the 13-cycle
> that has the same breathing amplitude as the seed phase at 3.

Lean proves:

```lean
REST_unique : ∀ i, isREST i → i = 10
```

Therefore, any `restPhase` satisfying `isREST restPhase` and `< 13`
must satisfy `restPhase = 10`.

## 3. Canonical Parameters and Uniqueness

We define `UFRF.Params.canonical` by:

* `phi       := (1 + √5)/2`
* `cycleLen  := 13`
* `restPhase := 10`

and prove the main uniqueness theorem:

```lean
theorem UFRF.Params.params_unique (A : Params) : A = Params.canonical
```

This uses:

* the uniqueness of the >1 root of `φ^2 = φ + 1`,
* the axiom `cycleLen_13`,
* and `REST_unique` plus the `restPhase_rest` axiom.

Thus any admissible UFRF parameter set collapses to the canonical one.
There are **no free parameters** at this scale.

## 4. Moonshine Consequences

`lean/UFRF/Moonshine.lean` lifts these parameters into the Monster
Moonshine construction:

* `jCoeff (A : Params) (n : ℤ) : ℤ` – wraps `Monster_Moonshine.monster_coeff`.
* `B2 (A : Params) : ℝ` – wraps `Monster_Moonshine.monster_B2`.

Lean proves invariance:

```lean
jCoeff_param_invariant : ∀ A₁ A₂ n, jCoeff A₁ n = jCoeff A₂ n
B2_param_invariant     : ∀ A₁ A₂, B2 A₁ = B2 A₂
```

and concrete values:

```lean
jCoeff_one_for_all : ∀ A, jCoeff A 1 = 196884
B2_for_all_params  : ∀ A, B2 A = 196884 * 169 / (744 * 60)
```

Therefore, the Moonshine constants used in this repo are *not* fitted.
They are uniquely fixed by the UFRF axioms and the Monster data.

## Files

- `lean/UFRF/Params.lean` – parameter structure and uniqueness theorem
- `lean/UFRF/Moonshine.lean` – parametric wrappers and invariance proofs
- `lean/ZPartition.lean` – parametric partition function integration

## See Also

- `docs/PARAMS_INTEGRATION.md` – detailed integration notes
- `docs/PARAMS_COMPLETE.md` – complete implementation details
- `docs/UFRF_ASSUMPTIONS.md` – UFRF axioms and assumptions
