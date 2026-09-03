import Mathlib
import P2M.Util
import P2M.Sol.S_AlgEquiv_algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank

set_option autoImplicit false

theorem AlgEquiv.algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank
    (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (hσ : orderOf σ = Module.finrank F E) (c : E) :
    algebraMap F E (LinearMap.det ((σ : E →ₐ[F] E).toLinearMap - c • (LinearMap.id : E →ₗ[F] E))) =
      (-1) ^ (Module.finrank F E - 1) *
        (1 - ∏ i ∈ Finset.range (Module.finrank F E), (σ ^ i) c) := by p2m_exact_reverting @_root_.P2MW.S_AlgEquiv_algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank.solution
