import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_le_of_forall_mem_support_exists_specializes_map_germ_le

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.IdealSheafData.le_of_forall_mem_support_exists_specializes_map_germ_le
    {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ x : X, x ∈ (J.support : Set X) →
      ∃ (y : X) (_ : x ⤳ y) (U : X.affineOpens) (hy : y ∈ (U : X.Opens)),
        Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (I.ideal U) ≤
          Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (J.ideal U)) :
    I ≤ J := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_le_of_forall_mem_support_exists_specializes_map_germ_le.solution
