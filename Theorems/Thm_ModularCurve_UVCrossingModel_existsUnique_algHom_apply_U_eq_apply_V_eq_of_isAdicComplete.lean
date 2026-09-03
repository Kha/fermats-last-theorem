import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete
    {W : Type*} [CommRing W] (π : W) {C : Type*} [CommRing C] [Algebra W C]
    (I : Ideal C) [IsAdicComplete I C] (ξ η : C) (hξ : ξ ∈ I) (hη : η ∈ I) (h : ξ * η = algebraMap W C π) :
    ∃! φ : UVCrossingModel W π →ₐ[W] C, φ (U π) = ξ ∧ φ (V π) = η := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete.solution
