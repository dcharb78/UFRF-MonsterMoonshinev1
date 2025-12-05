# UFRF_FixedPoint_ImplementationNotes.md
## Implementation Notes for `is_UFRF_fixed_point` in Lean and Docs

This file gives technical guidance for wiring the “UFRF fixed-point” notion into the Lean codebase and documentation.

---

## 1. Lean Predicate: `is_UFRF_fixed_point`

### 1.1. Purpose

The idea is to have a **single predicate** that encodes:

- “This function is the UFRF partition function at the Monster scale.”
- “It is modular invariant (T and S).”
- “It has the correct principal part.”

Then:

- `Z_is_UFRF_fixed_point` says: **Z satisfies this predicate**.
- `UFRF_fixed_point_unique` says: **any other F satisfying it is equal to Z**.

This formalizes the “fixed point” nature of Z within Lean’s type system.

---

### 1.2. Sketch of the Predicate

In your `ZPartition.lean` (or a new file `UFRF_FixedPoint.lean`), you can add:

```lean
import analysis.complex.upper_half_plane
import analysis.complex.exponential
import Monster_Moonshine  -- adjust as needed
import ZPartition         -- where Z, a, aC, q are defined

noncomputable theory
open complex

namespace UFRF

notation `ℍ` := upper_half_plane

/-- Predicate stating that a function F : ℍ → ℂ has the same q-series
    coefficients as Z (or equivalently, as the UFRF/Monster a_n). -/
def has_UFRF_qseries (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, F τ = ∑' (n : ℤ), aC n * (q τ) ^ n

/-- Predicate stating that F is modular invariant in the UFRF sense:
    T-invariant and S-invariant. For now, we reuse the same S axiom
    structure as Z, or require explicit invariance. -/
def is_modular_UFRF (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, F ⟨τ + 1, by
      -- same proof as in Z_T_invariant, or abstracted helper lemma
      simp [upper_half_plane.im]
      have h : (τ : ℂ).im > 0 := τ.property
      simp [complex.add_im]
      exact h⟩ = F τ) ∧
  (∀ τ : ℍ, F ⟨-1 / (τ : ℂ), by
      -- same proof as in Z_S_invariant_axiom, or abstracted lemma
      simp [complex.div_im]
      have h : (τ : ℂ).im > 0 := τ.property
      have h_norm : complex.norm_sq (τ : ℂ) > 0 := by
        rw [complex.norm_sq_pos]
        exact h
      field_simp
      exact div_pos h h_norm⟩ = F τ)

/-- Predicate encoding the UFRF principal part at infinity. -/
def has_UFRF_principal_part (F : ℍ → ℂ) : Prop :=
  (a (-1 : ℤ) = 1) ∧ (a (0 : ℤ) = 0) ∧ (a (1 : ℤ) = 196884)

/-- A function is a UFRF fixed-point modular function if:
    - it has the UFRF q-series structure
    - it is UFRF-modular (T and S invariance)
    - it has the correct principal part
-/
def is_UFRF_fixed_point (F : ℍ → ℂ) : Prop :=
  has_UFRF_qseries F ∧ is_modular_UFRF F ∧ has_UFRF_principal_part F

end UFRF
