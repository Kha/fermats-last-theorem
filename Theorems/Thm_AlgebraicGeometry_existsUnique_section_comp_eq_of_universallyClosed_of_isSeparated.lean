import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] [IsSeparated f]
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! σ : Spec (CommRingCat.of R) ⟶ X,
      σ ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated.solution
