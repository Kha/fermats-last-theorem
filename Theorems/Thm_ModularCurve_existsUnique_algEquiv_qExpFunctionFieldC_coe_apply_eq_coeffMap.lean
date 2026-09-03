import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one

theorem ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ₀ : ModularCurve.qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] ModularCurve.qExpFunctionFieldC K₀ Γ) :
    ∃! σ : ModularCurve.qExpFunctionFieldC K Γ ≃ₐ[K] ModularCurve.qExpFunctionFieldC K Γ,
      ∀ (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ),
        (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀) →
        ((σ x : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) =
          ModularCurve.coeffMap φ ((σ₀ x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) : LaurentSeries K₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap.solution
