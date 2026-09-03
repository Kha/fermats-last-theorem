import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.map_stalkMap_maximalIdeal_eq_of_etale_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) [AlgebraicGeometry.Etale (W.ι ≫ f)] (x : X) (hx : x ∈ W) :
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict.solution
