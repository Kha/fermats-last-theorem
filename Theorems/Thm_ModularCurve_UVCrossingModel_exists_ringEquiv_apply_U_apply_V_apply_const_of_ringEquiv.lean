import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_apply_U_apply_V_apply_const_of_ringEquiv

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_apply_U_apply_V_apply_const_of_ringEquiv
    (W W' : Type) [CommRing W] [CommRing W'] (ρ : W ≃+* W') (π : W) :
    ∃ θ : UVCrossingModel W π ≃+* UVCrossingModel W' (ρ π),
      θ (U π) = U (ρ π) ∧ θ (V π) = V (ρ π) ∧ ∀ w : W, θ (const π w) = const (ρ π) (ρ w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_apply_U_apply_V_apply_const_of_ringEquiv.solution
