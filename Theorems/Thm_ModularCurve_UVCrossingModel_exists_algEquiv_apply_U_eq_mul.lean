import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_algEquiv_apply_U_eq_mul

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_algEquiv_apply_U_eq_mul
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] (π : Ô) (hπu : ¬ IsUnit π) (γ : (UVCrossingModel Ô π)ˣ) :
    ∃ τ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π,
      τ (U π) = (γ : UVCrossingModel Ô π) * U π ∧ τ (V π) = (↑γ⁻¹ : UVCrossingModel Ô π) * V π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_algEquiv_apply_U_eq_mul.solution
