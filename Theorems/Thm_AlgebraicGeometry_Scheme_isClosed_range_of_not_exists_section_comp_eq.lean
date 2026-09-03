import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.isClosed_range_of_not_exists_section_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hns : ¬ ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x) :
    IsClosed (Set.range x.base) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq.solution
