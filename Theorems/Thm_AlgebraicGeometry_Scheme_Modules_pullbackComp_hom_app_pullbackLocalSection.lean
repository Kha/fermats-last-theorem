import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection f
          (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection g s)) =
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection (f ≫ g) s :
        Γ((AlgebraicGeometry.Scheme.Modules.pullback (f ≫ g)).obj M, f ⁻¹ᵁ (g ⁻¹ᵁ U))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection.solution
