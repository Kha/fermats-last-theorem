import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
    {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) (g : Γ(Y, U)) :
    (Scheme.Modules.pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.toUnitSection U g)) =
      Scheme.Modules.toUnitSection (φ ⁻¹ᵁ U) (φ.app U g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2.solution
