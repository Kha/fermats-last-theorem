import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_ncard_irreducibleComponents_pullback_toBase_eq_ncard_minimalPrimes_of_surjective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel~iotaInf_mem_range_iotaFin_iff"

theorem AlgebraicCurve.TwoChartIntegralModel.ncard_irreducibleComponents_pullback_toBase_eq_ncard_minimalPrimes_of_surjective
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (ϖ : R) (κ : Type u) [Field κ] [Algebra R κ]
    (hsurj : Function.Surjective (algebraMap R κ)) (hker : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ})
    (hInf : ∀ Q ∈ (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes,
      (jInvChartInf R F j : ↥(chartAlgInf R F j)) ∉ Q) :
    (irreducibleComponents ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))).ncard =
      (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes.ncard := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ncard_irreducibleComponents_pullback_toBase_eq_ncard_minimalPrimes_of_surjective.solution
