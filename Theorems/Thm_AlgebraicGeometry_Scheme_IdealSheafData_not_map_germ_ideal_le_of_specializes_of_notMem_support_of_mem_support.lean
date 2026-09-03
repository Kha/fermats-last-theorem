import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_not_map_germ_ideal_le_of_specializes_of_notMem_support_of_mem_support

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.not_map_germ_ideal_le_of_specializes_of_notMem_support_of_mem_support
    {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.affineOpens) (x ξ : ↥X) (hx : x ∈ (U : X.Opens)) (hξx : ξ ⤳ x)
    (hξI : ξ ∉ (I.support : Set ↥X)) (hξJ : ξ ∈ (J.support : Set ↥X)) :
    ¬ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom ≤ (J.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_not_map_germ_ideal_le_of_specializes_of_notMem_support_of_mem_support.solution
