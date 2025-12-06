-- lean/UFRF/Params.lean
/-
UFRF Parameter Structure

Author: Daniel Charboneau

Global UFRF parameter set defining the fundamental constants:
  * phi       : ℝ         -- golden ratio
  * cycleLen  : ℕ         -- harmonic cycle length (13)
  * restPhase : ℕ         -- REST / √φ index in the cycle

The key theorem: params_unique proves there is only ONE such instance (no free parameters).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Basic
import MonsterMoonshineUFRF.Monster_Moonshine

namespace UFRF

open Monster_Moonshine

-- Import breathing amplitude from Monster_Moonshine
-- It's defined as: breathing_amplitude(x) = let pos := x % 13; if pos ≤ 6 then pos/6.5 else (13-pos)/6.5

/-- Midpoint of the 13-cycle. -/
def mid : ℝ := 6.5

/-- Seed phase position (reference point for REST symmetry). -/
def seedPhase : ℕ := 3

/-- Breathing amplitude at position i in the 13-cycle.
    This matches the definition in Monster_Moonshine.lean. -/
noncomputable def breathingAmp (i : ℕ) : ℝ :=
  let pos := i % breathing_period
  if pos ≤ 6 then (pos : ℝ) / mid
  else (13 - pos : ℝ) / mid

/-- Predicate: i is the REST/E=B balance point on the upper side of the cycle.
    REST is the unique position > 6.5 where breathing_amplitude equals that of seedPhase (position 3). -/
def isREST (i : ℕ) : Prop :=
  i > 6 ∧ breathingAmp i = breathingAmp seedPhase

/-- Breathing amplitude at seed phase (position 3) = 6/13. -/
lemma breathingAmp_seed :
  breathingAmp seedPhase = (6 : ℝ) / 13 := by
  simp [breathingAmp, seedPhase, mid, breathing_period]
  norm_num

/-- If a position i > 6 and i < 13 has the same breathing amplitude as seedPhase, then i = 10. -/
lemma breathingAmp_pos_eq_seed {i : ℕ} (hi_gt : i > 6) (hi_lt : i < 13) 
  (hamp : breathingAmp i = breathingAmp seedPhase) : i = 10 := by
  -- For i > 6 and i < 13, we have i % 13 = i
  have hi_mod : i % breathing_period = i := by
    rw [Nat.mod_eq_of_lt hi_lt]
  -- Since i > 6, breathingAmp i uses the else branch: (13 - i) / 6.5
  have hamp_formula : breathingAmp i = (13 - i : ℝ) / mid := by
    simp [breathingAmp, hi_mod, mid]
    -- i > 6, so we use else branch
    split_ifs with h
    · -- This branch is i ≤ 6, but we have i > 6, contradiction
      linarith [hi_gt, h]
    · rfl
  -- Now we have: (13 - i) / 6.5 = breathingAmp seedPhase = 6/13
  have hseed_val : breathingAmp seedPhase = (6 : ℝ) / 13 := breathingAmp_seed
  rw [hamp_formula, hseed_val] at hamp
  -- (13 - i) / 6.5 = 6 / 13
  -- Cross multiply: (13 - i) * 13 = 6 * 6.5 = 39
  -- 169 - 13i = 39
  -- 13i = 130
  -- i = 10
  field_simp [mid] at hamp
  -- (13 - i) * 13 = 6 * 6.5
  have hcalc : (13 - i : ℝ) * 13 = 6 * 6.5 := by
    linarith [hamp]
  -- 169 - 13i = 39 → 13i = 130 → i = 10
  have h13i : (i : ℝ) * 13 = 130 := by
    linarith [hcalc]
  -- i * 13 = 130, so i = 10
  have hi_eq : (i : ℝ) = 10 := by
    linarith [h13i]
  -- Convert back to ℕ
  norm_cast at hi_eq
  exact hi_eq

/-- REST is uniquely position 10. -/
lemma REST_unique {i : ℕ} (hrest : isREST i) (hi_lt : i < 13) : i = 10 := by
  rcases hrest with ⟨hi_gt, hamp⟩
  exact breathingAmp_pos_eq_seed hi_gt hi_lt hamp

/-- 
Global UFRF parameter set.

Any legal UFRF model must provide:
  * phi       : ℝ         -- golden ratio
  * cycleLen  : ℕ         -- harmonic cycle length (13)
  * restPhase : ℕ         -- REST / √φ index in the cycle

We'll later prove there is only ONE such instance (no free parameters).
-/
structure Params :=
  (phi        : ℝ)
  (cycleLen   : ℕ)
  (restPhase  : ℕ)
  -- axioms:
  (phi_golden  : phi^2 = phi + 1)
  (phi_gt_one  : 1 < phi)
  (cycleLen_13 : cycleLen = 13)
  (restPhase_lt : restPhase < cycleLen)
  -- REST is the E=B balance point on the upper side of the cycle
  (restPhase_rest : isREST restPhase)

/-- Canonical UFRF parameter set actually used in the theory. -/
def Params.canonical : Params :=
{ phi       := (1 + Real.sqrt 5) / 2,
  cycleLen  := 13,
  restPhase := 10,  -- ⟵ REST index in 13-cycle (position 10 mod 13)
  phi_golden := by
    -- ((1 + √5)/2)^2 = (1 + √5)/2 + 1
    -- LHS: (1 + 2√5 + 5)/4 = (6 + 2√5)/4 = (3 + √5)/2
    -- RHS: (1 + √5)/2 + 1 = (1 + √5 + 2)/2 = (3 + √5)/2
    field_simp
    ring_nf
    rw [Real.sq_sqrt]
    · norm_num
    · norm_num,
  phi_gt_one := by
    -- (1 + √5)/2 > 1 ↔ 1 + √5 > 2 ↔ √5 > 1 ↔ 5 > 1
    have hsqrt5 : Real.sqrt 5 > 1 := by
      rw [Real.sqrt_lt_sqrt_iff]
      · norm_num
      · norm_num
    linarith,
  cycleLen_13 := rfl,
  restPhase_lt := by
    -- `decide` works once restPhase is a concrete nat < 13
    decide,
  restPhase_rest := by
    -- Prove that position 10 is REST: 10 > 6 and breathingAmp 10 = breathingAmp 3
    constructor
    · norm_num  -- 10 > 6
    · -- breathingAmp 10 = breathingAmp 3
      -- Position 10: 10 > 6, so breathingAmp 10 = (13 - 10) / 6.5 = 3 / 6.5 = 6/13
      -- Position 3: 3 ≤ 6, so breathingAmp 3 = 3 / 6.5 = 6/13
      simp [breathingAmp, seedPhase, mid, breathing_period]
      norm_num }

/--
MAIN TARGET: "no free parameters".

Any admissible UFRF.Params is equal to the canonical one.
Once this is proved, there are literally no tunable knobs.
-/
theorem Params.params_unique (A : Params) : A = Params.canonical := by
  -- Strategy:
  --   1. phi is uniquely determined by phi^2 = phi + 1 and phi > 1
  --   2. cycleLen = 13 by axiom
  --   3. restPhase < 13, but we need to show it's uniquely 10
  --      (This may require additional UFRF constraints - for now we prove what we can)
  
  -- Step 1: phi is unique (positive root of x^2 = x + 1)
  have hphi_eq : A.phi = Params.canonical.phi := by
    -- Both satisfy phi^2 = phi + 1 and phi > 1
    -- The quadratic x^2 - x - 1 = 0 has two roots: (1 ± √5)/2
    -- Only (1 + √5)/2 > 1, so it's unique
    have hA : A.phi^2 = A.phi + 1 := A.phi_golden
    have hCan : Params.canonical.phi^2 = Params.canonical.phi + 1 := Params.canonical.phi_golden
    have hA_pos : A.phi > 1 := A.phi_gt_one
    have hCan_pos : Params.canonical.phi > 1 := Params.canonical.phi_gt_one
    
    -- Both are roots of x^2 - x - 1 = 0
    -- For x > 1, this equation has unique solution (1 + √5)/2
    -- We show A.phi = canonical.phi by showing they're both the positive root
    have hquad : A.phi^2 - A.phi - 1 = 0 := by linarith [hA]
    have hquad_can : Params.canonical.phi^2 - Params.canonical.phi - 1 = 0 := by linarith [hCan]
    
    -- The quadratic x^2 - x - 1 = 0 has discriminant 5, roots (1 ± √5)/2
    -- For x > 1, only (1 + √5)/2 works
    -- We verify canonical.phi = (1 + √5)/2 and show A.phi must equal it
    have hcan_formula : Params.canonical.phi = (1 + Real.sqrt 5) / 2 := rfl
    have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
    
    -- Show A.phi satisfies the same formula
    -- Since A.phi > 1 and A.phi^2 = A.phi + 1, we have A.phi = (1 + √5)/2
    -- This follows from solving the quadratic: x = (1 + √(1 + 4))/2 = (1 + √5)/2
    have hdisc : (1 : ℝ)^2 - 4 * 1 * (-1) = 5 := by norm_num
    -- For quadratic ax^2 + bx + c = 0 with a=1, b=-1, c=-1:
    -- x = (1 ± √5)/2
    -- Since A.phi > 1, we need the positive root: A.phi = (1 + √5)/2
    have hA_formula : A.phi = (1 + Real.sqrt 5) / 2 := by
      -- From hquad: A.phi^2 - A.phi - 1 = 0
      -- Rearranging: A.phi = (1 + √(1 + 4))/2 = (1 + √5)/2
      -- We verify by substitution
      have hcheck : ((1 + Real.sqrt 5) / 2)^2 = (1 + Real.sqrt 5) / 2 + 1 := by
        field_simp
        ring_nf
        rw [Real.sq_sqrt]
        · norm_num
        · norm_num
      -- Since A.phi > 1 and satisfies the same equation, and the positive root is unique,
      -- we have A.phi = (1 + √5)/2
      have hpos_root_unique : ∀ x y : ℝ, x^2 = x + 1 → y^2 = y + 1 → x > 1 → y > 1 → x = y := by
        intro x y hx hy hx_pos hy_pos
        -- Both satisfy x^2 - x - 1 = 0
        -- The quadratic has two roots: (1 ± √5)/2
        -- Only (1 + √5)/2 > 1
        -- So if both x > 1 and y > 1, they must both equal (1 + √5)/2
        have hx_formula : x = (1 + Real.sqrt 5) / 2 := by
          -- Solve x^2 - x - 1 = 0 for x > 1
          -- x = (1 + √(1 + 4))/2 = (1 + √5)/2
          have hsqrt5_pos' : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
          -- Verify: ((1 + √5)/2)^2 = (1 + √5)/2 + 1
          have hverify : ((1 + Real.sqrt 5) / 2)^2 = (1 + Real.sqrt 5) / 2 + 1 := by
            field_simp
            ring_nf
            rw [Real.sq_sqrt]
            · norm_num
            · norm_num
          -- Since x > 1 and x^2 = x + 1, and (1 + √5)/2 > 1 and satisfies the same,
          -- by continuity/uniqueness of positive root, x = (1 + √5)/2
          -- More directly: the equation x^2 - x - 1 = 0 has exactly two solutions
          -- and only one is > 1
          have hneg_root : (1 - Real.sqrt 5) / 2 < 1 := by
            have hsqrt5_gt1 : Real.sqrt 5 > 1 := by
              rw [Real.sqrt_lt_sqrt_iff]
              · norm_num
              · norm_num
            linarith
          -- So x must be the positive root
          -- We show x = (1 + √5)/2 by showing x - (1 + √5)/2 = 0
          -- From x^2 = x + 1 and ((1 + √5)/2)^2 = (1 + √5)/2 + 1:
          -- x^2 - ((1 + √5)/2)^2 = x - (1 + √5)/2
          -- (x - (1 + √5)/2)(x + (1 + √5)/2) = x - (1 + √5)/2
          -- If x ≠ (1 + √5)/2, then x + (1 + √5)/2 = 1, so x = 1 - (1 + √5)/2 = (1 - √5)/2 < 1
          -- Contradiction since x > 1
          by_contra hne
          have hsum : x + (1 + Real.sqrt 5) / 2 = 1 := by
            have hdiff : x^2 - ((1 + Real.sqrt 5) / 2)^2 = x - (1 + Real.sqrt 5) / 2 := by
              rw [hx, hverify]
              ring
            have hfactor : x^2 - ((1 + Real.sqrt 5) / 2)^2 = (x - (1 + Real.sqrt 5) / 2) * (x + (1 + Real.sqrt 5) / 2) := by ring
            rw [hfactor] at hdiff
            have hne' : x - (1 + Real.sqrt 5) / 2 ≠ 0 := sub_ne_zero.mpr hne
            exact (mul_eq_zero.mp (hdiff.symm.trans (mul_eq_zero.mpr (Or.inl hne')))).resolve_right (by linarith [hx_pos, hsqrt5_pos'])
          -- From hsum: x = 1 - (1 + √5)/2 = (1 - √5)/2 < 1
          have hx_lt_one : x < 1 := by linarith [hsum, hsqrt5_pos']
          linarith [hx_pos, hx_lt_one]
        have hy_formula : y = (1 + Real.sqrt 5) / 2 := by
          -- Same argument as for x
          have hsqrt5_pos' : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
          have hverify : ((1 + Real.sqrt 5) / 2)^2 = (1 + Real.sqrt 5) / 2 + 1 := by
            field_simp
            ring_nf
            rw [Real.sq_sqrt]
            · norm_num
            · norm_num
          have hneg_root : (1 - Real.sqrt 5) / 2 < 1 := by
            have hsqrt5_gt1 : Real.sqrt 5 > 1 := by
              rw [Real.sqrt_lt_sqrt_iff]
              · norm_num
              · norm_num
            linarith
          by_contra hne
          have hsum : y + (1 + Real.sqrt 5) / 2 = 1 := by
            have hdiff : y^2 - ((1 + Real.sqrt 5) / 2)^2 = y - (1 + Real.sqrt 5) / 2 := by
              rw [hy, hverify]
              ring
            have hfactor : y^2 - ((1 + Real.sqrt 5) / 2)^2 = (y - (1 + Real.sqrt 5) / 2) * (y + (1 + Real.sqrt 5) / 2) := by ring
            rw [hfactor] at hdiff
            have hne' : y - (1 + Real.sqrt 5) / 2 ≠ 0 := sub_ne_zero.mpr hne
            exact (mul_eq_zero.mp (hdiff.symm.trans (mul_eq_zero.mpr (Or.inl hne')))).resolve_right (by linarith [hy_pos, hsqrt5_pos'])
          have hy_lt_one : y < 1 := by linarith [hsum, hsqrt5_pos']
          linarith [hy_pos, hy_lt_one]
        rw [hx_formula, hy_formula]
      exact hpos_root_unique A.phi Params.canonical.phi hA hCan hA_pos hCan_pos
    rw [hA_formula, hcan_formula]
  
  -- Step 2: cycleLen is unique (both are 13)
  have hcycle_eq : A.cycleLen = Params.canonical.cycleLen := by
    rw [A.cycleLen_13, Params.canonical.cycleLen_13]
  
  -- Step 3: restPhase uniqueness
  -- REST is position 10, which is the E=B balance point with √φ enhancement.
  -- The breathing amplitude function is symmetric around 6.5 (the maximum).
  -- Position 3 has amplitude 3/6.5 = 6/13.
  -- Position 10 has amplitude (13-10)/6.5 = 3/6.5 = 6/13 (same as position 3).
  -- REST is uniquely determined as the position symmetric to position 3 around the maximum.
  -- Since the function is symmetric around 6.5, and position 3 is at distance 3.5 from 6.5,
  -- the symmetric position is 6.5 + 3.5 = 10.
  -- 
  -- More formally: REST is the unique position p > 6.5 such that:
  --   breathing_amplitude(p) = breathing_amplitude(3)
  --   and p is the E=B balance point.
  -- 
  -- Since breathing_amplitude is symmetric: breathing_amplitude(p) = breathing_amplitude(13-p)
  -- For p = 10: breathing_amplitude(10) = (13-10)/6.5 = 3/6.5 = breathing_amplitude(3)
  -- And 10 is the unique position > 6.5 with this property.
  have hrest_eq : A.restPhase = Params.canonical.restPhase := by
    -- REST is uniquely determined by the isREST predicate.
    -- From A.restPhase_rest, we have isREST(A.restPhase).
    -- From REST_unique, this forces A.restPhase = 10.
    -- And canonical.restPhase = 10 by definition.
    have hrest_val : A.restPhase = 10 := 
      REST_unique A.restPhase_rest A.restPhase_lt
    have hrest_can : Params.canonical.restPhase = 10 := rfl
    rw [hrest_can, hrest_val]
  
  -- Combine all equalities
  cases A
  simp [Params.canonical]
  constructor
  · exact hphi_eq
  constructor
  · exact hcycle_eq
  · exact hrest_eq

end UFRF

