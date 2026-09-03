import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_iff_apply_closedPoint_mem_range
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K : Type u} [Field K] (x : Spec (CommRingCat.of K) ⟶ X) :
    (∃ z : Spec (CommRingCat.of K) ⟶ Z, z ≫ i = x) ↔
      x.base (IsLocalRing.closedPoint K) ∈ Set.range i.base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range.solution
