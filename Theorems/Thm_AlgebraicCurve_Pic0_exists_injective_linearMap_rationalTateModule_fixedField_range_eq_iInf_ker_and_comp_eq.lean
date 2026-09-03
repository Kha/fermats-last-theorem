import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one

set_option autoImplicit false

open scoped TensorProduct

theorem AlgebraicCurve.Pic0.exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
    {k : Type} [Field k] [IsAlgClosed k] {F : Type} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (G : Subgroup (F ≃ₐ[k] F)) [Finite G]
    [AlgebraicCurve.IsCurveOver k ↥(IntermediateField.fixedField G)]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ Φ : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k ↥(IntermediateField.fixedField G)) →ₗ[ℚ_[ℓ]]
        ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k F),
      Function.Injective Φ ∧
      LinearMap.range Φ =
        ⨅ g : G, LinearMap.ker
          (ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k F) (F ≃ₐ[k] F) (g : F ≃ₐ[k] F) - 1) ∧
      ∀ (σ : F ≃ₐ[k] F)
        (τ : ↥(IntermediateField.fixedField G) ≃ₐ[k] ↥(IntermediateField.fixedField G)),
        (∀ y : ↥(IntermediateField.fixedField G), σ (y : F) = ((τ y : ↥(IntermediateField.fixedField G)) : F)) →
          Φ ∘ₗ ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k ↥(IntermediateField.fixedField G))
              (↥(IntermediateField.fixedField G) ≃ₐ[k] ↥(IntermediateField.fixedField G)) τ =
            ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k F) (F ≃ₐ[k] F) σ ∘ₗ Φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq.solution
