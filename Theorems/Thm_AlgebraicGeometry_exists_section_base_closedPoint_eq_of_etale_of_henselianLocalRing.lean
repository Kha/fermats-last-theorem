import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [AlgebraicGeometry.Etale f]
    (x : X) (hx : f.base x = IsLocalRing.closedPoint R) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing.solution
