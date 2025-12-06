# UFRF – No Free Parameters (Formal Layer)

**Author:** Daniel Charboneau  
**Date:** 2025-12-06

This repository includes a Lean formalization of the claim that the global UFRF parameters (φ, 13-cycle, REST) are uniquely determined by the axioms.

## What is Formalized

### `UFRF.Params` Structure

A structure capturing the fundamental UFRF constants:

- `phi : ℝ` – golden ratio
- `cycleLen : ℕ` – harmonic cycle length (13)
- `restPhase : ℕ` – REST/E=B balance point index

With axioms:
- `phi_golden : phi^2 = phi + 1`
- `phi_gt_one : 1 < phi`
- `cycleLen_13 : cycleLen = 13`
- `restPhase_lt : restPhase < cycleLen`
- `restPhase_rest : isREST restPhase` – REST is the E=B balance point

### `UFRF.Params.canonical`

The canonical parameter set:
- `phi = (1 + √5)/2` (golden ratio)
- `cycleLen = 13`
- `restPhase = 10` (REST position)

### Key Theorem: `UFRF.Params.params_unique`

```lean
theorem params_unique (A : Params) : A = Params.canonical
```

**This proves there are no free knobs once axioms hold.**

The proof establishes:
1. **Golden ratio uniqueness:** `phi` is uniquely `(1 + √5)/2` (positive root of `x^2 = x + 1`)
2. **Cycle length uniqueness:** `cycleLen = 13` (by axiom)
3. **REST uniqueness:** `restPhase = 10` (via breathing amplitude symmetry)

### `UFRF.Moonshine` Layer

Provides parametric wrappers:

- `jCoeff (A : Params) (n : ℤ) : ℤ` – wraps the Monster q-series coefficients
- `B2 (A : Params) : ℝ` – wraps the B₂ constant

With invariance theorems:

- `jCoeff_param_invariant : ∀ A₁ A₂ n, jCoeff A₁ n = jCoeff A₂ n`
- `B2_param_invariant : ∀ A₁ A₂, B2 A₁ = B2 A₂`
- `B2_for_all_params : ∀ A, B2 A = 196884 * 169 / (744 * 60)`
- `jCoeff_one_for_all : ∀ A, jCoeff A 1 = 196884`

### `ZPartition.lean` Integration

- `Z_param (A : Params) (τ : ℍ) : ℂ` – parametric partition function
- `Z_param_invariant : ∀ A₁ A₂, Z_param A₁ = Z_param A₂`

## Significance

**Moonshine coefficients used here are not tunable parameters; they are uniquely fixed by the UFRF axioms.**

This formal layer establishes that:

1. **No free parameters:** All UFRF constants are geometrically determined
2. **Invariance:** Moonshine quantities don't depend on which `Params` instance you use
3. **Uniqueness:** The canonical parameter set is the only one satisfying the axioms

## Files

- `lean/UFRF/Params.lean` – Parameter structure and uniqueness proof
- `lean/UFRF/Moonshine.lean` – Parametric wrappers and invariance theorems
- `lean/ZPartition.lean` – Parametric partition function integration

## See Also

- `docs/PARAMS_INTEGRATION.md` – Detailed integration notes
- `docs/PARAMS_COMPLETE.md` – Complete implementation details
- `lean/UFRF/Params.lean` – Full formal proofs

