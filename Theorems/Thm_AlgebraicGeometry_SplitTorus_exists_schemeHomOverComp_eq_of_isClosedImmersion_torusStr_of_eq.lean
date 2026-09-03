import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SplitTorus NeronModelInfra

theorem AlgebraicGeometry.SplitTorus.exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq
    (κ : Type) [Field κ] [IsAlgClosed κ] (t t' : ℕ) (ht : t' = t)
    (F : SchemeHomOver (torusStr κ t') (torusStr κ t)) (hF : IsClosedImmersion F.1) :
    ∀ y : SchemeHomOver (𝟙 _) (torusStr κ t),
      ∃ z : SchemeHomOver (𝟙 _) (torusStr κ t'), NeronModelInfra.schemeHomOverComp z F = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq.solution
