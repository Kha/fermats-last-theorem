import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) :
    genericPoint X ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2.solution
