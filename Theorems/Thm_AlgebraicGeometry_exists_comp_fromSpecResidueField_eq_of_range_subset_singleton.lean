import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
    {Z S : Scheme.{u}} [IsReduced Z] (g : Z ⟶ S) [QuasiCompact g]
    (s : S) (hs : IsClosed ({s} : Set S)) (hg : Set.range g.base ⊆ {s}) :
    ∃ t : Z ⟶ Spec (S.residueField s), t ≫ S.fromSpecResidueField s = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton.solution
