module

public import Mathlib
public import Definitions.Def_ModularCurve_LevelOneProlongationPair
public import Definitions.Def_ModularCurve_ModularUnit
public import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv

@[expose] public section
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing
theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hx : ((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
        ↥(modularFunctionFieldBar (1 * q))))⁻¹ ∈ R.R₁.integers)
    (h : ↥(modularFunctionFieldFullC (ResidueField A) 1))
    (hh : IsIntegral (Algebra.adjoin (ResidueField A)
      {(R.R₁.residue ⟨_, hx⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1))}) h) :
    ∃ f : R.R₁.integers,
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
        {(((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
        ↥(modularFunctionFieldBar (1 * q))))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))})
        (f : ↥(modularFunctionFieldBar (1 * q))) ∧
      R.R₁.residue f = h := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv.solution
