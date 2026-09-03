import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
    {X : Scheme.{u}} [IsIntegral X] (W : X.Opens) (s : X.functionField)
    (hs : ∀ x ∈ W, s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃! u : Γ(X, W), ∀ (x : X) (hx : x ∈ W),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx u) = s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range.solution
