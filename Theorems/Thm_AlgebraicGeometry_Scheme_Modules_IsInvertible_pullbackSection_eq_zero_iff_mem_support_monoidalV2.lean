import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support_monoidalV2

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support_monoidalV2
    {k : Type u} [Field k] {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (z : Spec (CommRingCat.of k) ⟶ X) :
    Scheme.Modules.pullbackSection z s = 0 ↔
      z.base (IsLocalRing.closedPoint k) ∈ (Scheme.Modules.zeroSchemeIdeal s).support := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support_monoidalV2.solution
