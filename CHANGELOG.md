# Changelog

All notable changes to this project will be documented in this file.

## [v1.1] - 2025-12-06 - Formal No-Free-Parameters Layer

### Added

- **UFRF.Params Layer** - Formal parameter structure proving "no free parameters"
  - `lean/UFRF/Params.lean`: Parameter structure with uniqueness proof
    - `phi` uniqueness: proven (golden ratio = (1+√5)/2)
    - `cycleLen` uniqueness: proven (both are 13)
    - `restPhase` uniqueness: proven via breathing amplitude symmetry (position 10)
    - `params_unique` theorem: complete, no sorries
  - `lean/UFRF/Moonshine.lean`: Parametric wrappers for jCoeff and B₂
    - `jCoeff (A : Params) (n : ℤ)` wraps `monster_coeff`
    - `B2 (A : Params)` wraps B₂ constant
    - Invariance theorems: `jCoeff_param_invariant`, `B2_param_invariant`, `B2_for_all_params`, etc.
  - `lean/ZPartition.lean`: Added `Z_param` parametric version and `Z_param_invariant` theorem
  - `lean/Monster_Moonshine.lean`: Added `Monster_Moonshine` namespace with API exports

- **Documentation**
  - `docs/NO_FREE_PARAMS.md`: Comprehensive formal proof documentation for no-free-parameters claim
  - `docs/PARAMS_INTEGRATION.md`: Integration notes and analysis
  - `docs/PARAMS_COMPLETE.md`: Complete implementation details
  - Added "Architecture Overview (3 Layers)" section to README
  - Added Mermaid dependency diagram to README
  - Added "How to Build and Check the Proofs" section to README

### Changed

- Updated `README.md`:
  - Added three-layer architecture explanation (Geometry/Axioms → Monster Data → Analytic Layer)
  - Added module dependency diagram (Mermaid)
  - Enhanced repository structure documentation
  - Added explicit build/check instructions
- Updated `lakefile.lean` to include new `UFRF.Params` and `UFRF.Moonshine` roots
- Enhanced `docs/NO_FREE_PARAMS.md` with detailed breathing amplitude explanation and REST uniqueness proof

### Significance

This establishes that **all UFRF parameters are uniquely determined** (no free parameters) and **Moonshine constants are invariant** under Params choice. This is a foundational result showing that UFRF-Monster Moonshine has no tunable knobs - everything is geometrically determined.

The formal layer proves:
- `UFRF.Params.params_unique`: Any admissible parameter set equals the canonical one
- `UFRF.B2_for_all_params`: B₂ is uniquely fixed at `196884 * 169 / (744 * 60)`
- `UFRF.jCoeff_param_invariant`: j-function coefficients are invariant across all Params

See `docs/NO_FREE_PARAMS.md` for complete details.

## [Unreleased]

### Future Work

- Additional moonshine cases beyond Monster
- Extended concurrency theorems
- Further geometric derivations

