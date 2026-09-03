import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_le_iff_map_germ_le

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_comap_le_iff_map_germ_le
    {X : Scheme.{u}} (e : X ≅ X) (I J : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) (V : X.affineOpens) (hV : e.hom.base x ∈ (V : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom ((I.comap e.hom).ideal U) ≤
        Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom ((J.comap e.hom).ideal U) ↔
      Ideal.map (X.presheaf.germ (V : X.Opens) (e.hom.base x) hV).hom (I.ideal V) ≤
        Ideal.map (X.presheaf.germ (V : X.Opens) (e.hom.base x) hV).hom (J.ideal V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_le_iff_map_germ_le.solution
