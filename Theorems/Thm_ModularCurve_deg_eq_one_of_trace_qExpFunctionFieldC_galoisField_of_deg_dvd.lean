import Mathlib
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.jqNModC_one CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (w : Place K ↥(qExpFunctionFieldC K Γ))

    (ι₁ : ↥(qExpFunctionFieldC (ZMod p) Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι₁ : ∀ x : ↥(qExpFunctionFieldC (ZMod p) Γ),
      (ι₁ x : LaurentSeries K) = coeffMap (ZMod.castHom (dvd_refl p) K) (x : LaurentSeries (ZMod p)))
    (P₁ : Place (ZMod p) ↥(qExpFunctionFieldC (ZMod p) Γ))
    (hP₁ : P₁.toValuationSubring = w.toValuationSubring.comap ι₁)

    (m : ℕ) (hm : 0 < m) (ι₀ : GaloisField p m →+* K)
    (ι : ↥(qExpFunctionFieldC (GaloisField p m) Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(qExpFunctionFieldC (GaloisField p m) Γ),
      (ι x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries (GaloisField p m)))
    (P : Place (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ))
    (hP : P.toValuationSubring = w.toValuationSubring.comap ι)
    (hdvd : P₁.deg ∣ m) :
    P.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd.solution
