import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre

set_option autoImplicit false

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre
    (R F : Type) [CommRing R] [IsLocalRing R] [Field F] [Algebra R F] (j : F)
    (V : ValuationSubring F)
    (hVR : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a : R, a ∈ maximalIdeal R → (⟨algebraMap R F a, hVR a⟩ : ↥V) ∈ maximalIdeal ↥V)
    (hVC : ∀ c : ↥(chartAlgFin R F j), (c : F) ∈ V)
    (y : Ideal ↥(chartAlgFin R F j))
    (hy : ∀ c : ↥(chartAlgFin R F j), c ∈ y ↔ ∀ hc : (c : F) ∈ V, (⟨(c : F), hc⟩ : ↥V) ∈ maximalIdeal ↥V)
    (hny : ¬ y.IsMaximal) :
    ∀ hjV : j ∈ V, ∀ p : Polynomial R, p.Monic → ∀ hp : Polynomial.aeval j (p.map (algebraMap R F)) ∈ V,
      (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre.solution
