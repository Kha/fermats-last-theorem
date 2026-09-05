module

public import Mathlib
public import Definitions.Def_ModularCurve_LevelOneProlongationPair
public import Definitions.Def_ModularCurve_ModularUnit
public import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing
theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) :
    ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers,
      ∃ y : LaurentSeries A, coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)) ∧
        ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst.solution
