import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.LogDeRham.pullbackPair_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

theorem ModularCurve.inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra κ K]
    (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (heK : ∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ, ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (g : LaurentSeries κ))
    (plK : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hplK : ∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) (v : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ)), (plK v).ord (eK g) = v.ord g)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) (hg : g ≠ 0)
    (E : AlgebraicCurve.Divisor.degZero (K := κ) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ))
    (hE : ∀ v : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ), (p : ℤ) * (E : AlgebraicCurve.Divisor κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ)) v = v.ord g) :
    (eK g)⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (eK g) = 0 ↔ AlgebraicCurve.Pic0.mk E = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord.solution
