module

public import Mathlib
public import Definitions.Def_ModularCurve_LevelOneProlongationPair
public import Definitions.Def_ModularCurve_ModularUnit
public import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing
theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1)⁻¹} :
          Set ↥(modularFunctionFieldFullC (ResidueField A) 1)))
      ↥(modularFunctionFieldFullC (ResidueField A) 1) = q - 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv.solution
