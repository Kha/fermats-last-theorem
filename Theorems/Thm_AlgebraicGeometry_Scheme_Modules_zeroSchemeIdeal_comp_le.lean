import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_le

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_comp_le
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') :
    Scheme.Modules.zeroSchemeIdeal (s ≫ f) ≤ Scheme.Modules.zeroSchemeIdeal s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_le.solution
