import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
    {X : Scheme} [IsIntegral X] {𝓛 𝓜 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (φ : 𝓛 ⟶ 𝓜) (U : X.Opens) (hU : (U : Set X).Nonempty)
    (h : (Scheme.Modules.pullback U.ι).map φ = 0) : φ = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral.solution
