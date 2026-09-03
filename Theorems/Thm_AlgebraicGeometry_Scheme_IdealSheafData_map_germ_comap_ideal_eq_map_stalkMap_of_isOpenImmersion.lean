import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (I : Y.IdealSheafData) (x : X)
    (U : Y.affineOpens) (hU : f.base x ∈ (U : Y.Opens)) (V : X.affineOpens) (hV : x ∈ (V : X.Opens)) :
    Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom ((I.comap f).ideal V) =
      Ideal.map (f.stalkMap x).hom (Ideal.map (Y.presheaf.germ (U : Y.Opens) (f.base x) hU).hom (I.ideal U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion.solution
