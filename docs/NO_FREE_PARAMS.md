# UFRF – No Free Parameters (Lean Formalization)

**Author:** Daniel Charboneau

This document summarizes how the repository formalizes the claim that the UFRF parameters at the Monster scale are uniquely determined by the axioms.

## 1. Global Parameter Structure

`lean/UFRF/Params.lean` defines:

- `structure UFRF.Params` with fields:
  - `phi : ℝ` – golden ratio
  - `cycleLen : ℕ` – harmonic cycle (13)
  - `restPhase : ℕ` – REST / E=B balance position

- Axioms:
  - `phi_golden : phi^2 = phi + 1` and `phi_gt_one : 1 < phi`
  - `cycleLen_13 : cycleLen = 13`
  - `restPhase_lt : restPhase < cycleLen`
  - `restPhase_rest : isREST restPhase`

`isREST` is defined using the **breathing amplitude**:

- `breathingAmp (i : ℕ) : ℝ` – symmetric about the midpoint 6.5
- `seedPhase : ℕ := 3`
- `isREST i :↔ i > 6 ∧ breathingAmp i = breathingAmp seedPhase`

From this, Lean proves:

- `REST_unique : ∀ i, isREST i → i = 10`

and uses it to set `Params.canonical.restPhase = 10`.

## 2. Uniqueness: No Free Parameters

The main theorem is:

```lean
theorem UFRF.Params.params_unique (A : Params) : A = Params.canonical
```

This encodes:

* φ is the unique >1 solution of `φ^2 = φ + 1`
* `cycleLen` must be 13
* `restPhase` must be the unique REST position (10) where E=B balance holds

Thus **any** `Params` satisfying the axioms collapses to `Params.canonical`. There is no remaining degree of freedom.

## 3. Moonshine Consequences

`lean/UFRF/Moonshine.lean` defines:

* `jCoeff (A : Params) (n : ℤ) : ℤ` – wraps `Monster_Moonshine.monster_coeff`
* `B2 (A : Params) : ℝ` – wraps `Monster_Moonshine.monster_B2`

and proves invariance:

* `jCoeff_param_invariant : ∀ A₁ A₂ n, jCoeff A₁ n = jCoeff A₂ n`
* `B2_param_invariant : ∀ A₁ A₂, B2 A₁ = B2 A₂`

plus concrete values:

* `jCoeff_one_for_all : ∀ A, jCoeff A 1 = 196884`
* `B2_for_all_params : ∀ A, B2 A = 196884 * 169 / (744 * 60)`

These theorems show that once the UFRF axioms are accepted, the Moonshine coefficients used in this project are **uniquely fixed** and cannot be tuned.

## Files

- `lean/UFRF/Params.lean` – parameter structure and uniqueness theorem
- `lean/UFRF/Moonshine.lean` – parametric wrappers and invariance proofs
- `lean/ZPartition.lean` – parametric partition function integration

## See Also

- `docs/PARAMS_INTEGRATION.md` – detailed integration notes
- `docs/PARAMS_COMPLETE.md` – complete implementation details
- `docs/UFRF_ASSUMPTIONS.md` – UFRF axioms and assumptions

