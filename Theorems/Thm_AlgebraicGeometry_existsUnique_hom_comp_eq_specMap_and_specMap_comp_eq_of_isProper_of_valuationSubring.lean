import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {K : Type u} [Field K] (A : ValuationSubring K)
    (ρ : R →+* ↥A)
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ)) :
    ∃! s : Spec (CommRingCat.of ↥A) ⟶ X,
      s ≫ f = Spec.map (CommRingCat.ofHom ρ) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ s = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring.solution
