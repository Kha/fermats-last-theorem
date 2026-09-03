import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~dense_setOf_exists_section_of_isAlgClosed"

theorem AlgebraicGeometry.Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] :
    Dense {x : {x : T // t.base x = IsLocalRing.closedPoint R} |
      ∃ s : Spec (CommRingCat.of R) ⟶ T, s ≫ t = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x.1} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed.solution
