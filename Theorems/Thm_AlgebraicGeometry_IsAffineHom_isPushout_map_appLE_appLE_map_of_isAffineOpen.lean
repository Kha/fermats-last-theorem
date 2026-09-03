import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineHom_isPushout_map_appLE_appLE_map_of_isAffineOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsAffineHom.isPushout_map_appLE_appLE_map_of_isAffineOpen
    {V W : Scheme.{u}} (γ : W ⟶ V) [IsAffineHom γ] {U U' : V.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    IsPushout (V.presheaf.map (homOfLE h).op) (γ.appLE U' (γ ⁻¹ᵁ U') le_rfl)
      (γ.appLE U (γ ⁻¹ᵁ U) le_rfl) (W.presheaf.map (homOfLE (γ.preimage_mono h)).op) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineHom_isPushout_map_appLE_appLE_map_of_isAffineOpen.solution
