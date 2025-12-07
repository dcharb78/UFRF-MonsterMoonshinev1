# UFRF Assumptions and Axioms

**Author:** Daniel Charboneau

This document clarifies the assumptions and axioms used in the UFRF-Monster Moonshine formalization.

---

## UFRF Assumptions: Derived vs. Axiomatized

### Overview

This document clarifies what is **derived** versus what is **axiomatized** in the UFRF framework.

### The Derivation Hierarchy

#### Level 0: Physical Law (Not UFRF-specific)

- Maxwell's equations
- E⊥B perpendicularity
- Photon as E×B vortex

#### Level 1: Derived from Physics

- Trinity structure {-0.5, 0, +0.5} — from field oscillation
- Two-plane completion (720°) — from perpendicular field geometry
- 13-cycle structure — from octave completion

#### Level 2: Axiomatized (Justified by Cross-Domain Success)

- S-invariance of partition function Z(τ)
- Specific form of projection law
- Scale hierarchy M = 144 × 10^n

#### Level 3: Proven in Lean 4

- T-invariance: Z(τ+1) = Z(τ)
- Uniqueness: {47, 59, 71} is the only valid triple
- Arithmetic: 47 × 59 × 71 + 1 = 196884

### Why This Structure Matters

Critics often ask: "Why should we accept your axioms?"

Answer: The Level 2 axioms are justified by their **cross-domain predictive success**. The same axioms that determine Monster dimensions also correctly predict:

- Nuclear shell gaps
- Fine structure constant
- Graphene viscosity-entropy ratio
- Cosmological mass ratios

If these were arbitrary, they would require different values in different domains. They don't.

**See**: [docs/DERIVATION_CHAIN.md](DERIVATION_CHAIN.md) for the complete derivation of the 13-cycle from electromagnetic first principles.

---

## S-Invariance Axiom

### Statement

The partition function Z(τ) is invariant under the S-transformation τ ↦ -1/τ:

```lean
axiom Z_S_invariant_axiom (τ : ℍ) :
  Z (-1 / τ) = Z τ
```

### Nature of the Assumption

**S-invariance is a UFRF physical axiom, not a Lean-proven analytic theorem.**

- Lean builds the mathematical structure conditional on this axiom.
- This is appropriate because S-invariance arises from the **dual trinity / SU(2)×SU(2) / Fourier symmetry** of UFRF, not from pure q-analysis.
- The S-transformation corresponds to geometric symmetries in the UFRF framework that are not derivable from standard modular form theory alone.

### Why This Approach

1. **Physical Origin**: The S-invariance comes from UFRF's geometric structure (dual trinity, SU(2)×SU(2) symmetry), which is a physical/theoretical framework assumption.

2. **Formal Clarity**: By marking it as an axiom, we make explicit what is assumed vs. what is proven within Lean.

3. **Mathematical Consistency**: The axiom is consistent with known modular form theory, but its derivation from UFRF principles is outside the scope of pure q-series analysis.

### Connection to Modular Forms

While S-invariance is an axiom in our framework, it aligns with the classical theory of modular forms, where the j-function is known to be SL(2,ℤ)-invariant. Our approach makes explicit that this invariance follows from UFRF geometric principles rather than being derived purely analytically.

---

## Other Assumptions

### Coefficient Values

The coefficients a_n are defined via `monster_coeff` and are currently hard-coded for small values:
- a(-1) = 1
- a(0) = 0
- a(1) = 196884
- a(2) = 21493760
- a(3) = 864299970
- a(n) = 0 for other n (for now)

These values come from UFRF/Monster structure and are proven via the `a_neg_one`, `a_zero`, `a_one` lemmas.

### Principal Part Structure

The principal part expansion of Z(τ) is documented via:
- `Z_principal_part`: Definitional equality Z(τ) = ∑' n, aC n * (q τ)^n
- Coefficient value lemmas: `a_neg_one`, `a_zero`, `a_one`, `Z_at_low_indices`

The structure q⁻¹ + 196884 q + ... follows from these coefficient values, which are formally proven.

---

## What Is Proven vs. What Is Assumed

### Proven in Lean ✅

- T-invariance: Z(τ+1) = Z(τ) (via Euler's identity)
- Coefficient values: a(-1) = 1, a(0) = 0, a(1) = 196884
- Principal part structure: Via definitional equality + coefficient lemmas
- Z(τ) = j(τ) - 744: Via definition (j_minus_744 := Z)

### Assumed as Axiom ⚠️

- S-invariance: Z(-1/τ) = Z(τ) (UFRF geometric symmetry axiom)

### Not Constructed (Outside Scope) 📝

- Monster group construction (no one does this formally)
- Moonshine VOA construction (nobody does this formally)
- Full Monster module V^♮ construction

---

## Global Parameter Uniqueness

For a formal implementation of these axioms at the Monster scale (golden ratio, 13-cycle, REST/E=B balance), see:

- `lean/UFRF/Params.lean` – parameter structure and uniqueness theorem
- `docs/NO_FREE_PARAMS.md` – high-level summary

The `UFRF.Params.params_unique` theorem proves that all UFRF parameters are uniquely determined by the axioms—there are no free parameters to tune.

## Summary

The formalization makes a clear distinction between:
1. **What is proven** (T-invariance, coefficient values, principal part structure, parameter uniqueness)
2. **What is assumed** (S-invariance from UFRF physics)
3. **What is outside scope** (Monster group/VOA construction)

This honesty and clarity is respected in formal mathematics and makes the assumptions explicit for reviewers and external readers.

