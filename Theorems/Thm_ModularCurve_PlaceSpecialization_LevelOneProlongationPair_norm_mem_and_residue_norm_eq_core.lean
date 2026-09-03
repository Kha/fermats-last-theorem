import Mathlib
import Definitions.Def_ModularCurve_GaussPencilAdapter
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_norm_mem_and_residue_norm_eq_core
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve
theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.norm_mem_and_residue_norm_eq_core
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
    [Algebra K₁ (modularFunctionFieldBar (1 * q))]
    [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]
    (R : P.LevelOneProlongationPair) [R.HasGaussTransport K₁]
    (y f : modularFunctionFieldBar (1 * q))
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hyint : IsIntegral (R.gaussBase K₁) y) (hfint : IsIntegral (R.gaussBase K₁) f)
    (hjS : PlaceSpecialization.jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : PlaceSpecialization.jqFun (q := q) ∈ R.gaussOrder K₁ y f)
    (hspan : Submodule.span K₁ (R.gaussOrder K₁ y f : Set (modularFunctionFieldBar (1 * q))) = ⊤)
    (hκ₁ : 0 < Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne)
    (hκ₂ : 0 < Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo)
    (hdeg : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne + Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo
      = Module.finrank K₁ (modularFunctionFieldBar (1 * q)))
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((LevelOneProlongationPair.ResOne.val R (R.rho₁ K₁ hy₁ hf₁ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((LevelOneProlongationPair.ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A)) :
    Algebra.norm K₁ f
        = algebraMap (R.gaussBase K₁) K₁ (Algebra.norm (R.gaussBase K₁) (⟨f, R.self_mem_gaussOrder y f⟩ : R.gaussOrder K₁ y f)) ∧
      IsLocalRing.residue (R.gaussBase K₁) (Algebra.norm (R.gaussBase K₁) (⟨f, R.self_mem_gaussOrder y f⟩ : R.gaussOrder K₁ y f))
        = Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₁ K₁ hy₁ hf₁ ⟨f, R.self_mem_gaussOrder y f⟩)
            * Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₂ K₁ hy₂ hf₂ ⟨f, R.self_mem_gaussOrder y f⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_norm_mem_and_residue_norm_eq_core.solution
