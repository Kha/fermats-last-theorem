import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal
    {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) :
    (Scheme.Modules.zeroSchemeIdeal s).comap F =
      Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal.solution
