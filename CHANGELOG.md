# Changelog

All notable changes to this project will be documented in this file.

## [Unreleased] - feat/ufrf-params-no-free

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
  - `NO_FREE_PARAMS.md`: Formal proof documentation for no-free-parameters claim
  - `docs/PARAMS_INTEGRATION.md`: Integration notes and analysis
  - `docs/PARAMS_COMPLETE.md`: Complete implementation details

### Changed

- Updated `README.md` to reference `NO_FREE_PARAMS.md` and new documentation
- Updated `lakefile.lean` to include new `UFRF.Params` and `UFRF.Moonshine` roots

### Significance

This establishes that **all UFRF parameters are uniquely determined** (no free parameters) and **Moonshine constants are invariant** under Params choice. This is a foundational result showing that UFRF-Monster Moonshine has no tunable knobs - everything is geometrically determined.

See `NO_FREE_PARAMS.md` for complete details.

