import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Spec_exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Spec.exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq
    {A : Type} [CommRing A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (L : Type) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L 𝔭]
    {X : Scheme.{0}} (y y' : Spec (CommRingCat.of A) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y') :
    ∃ f : A, f ∉ 𝔭 ∧ ∀ (Af : Type) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af],
      Spec.map (CommRingCat.ofHom (algebraMap A Af)) ≫ y = Spec.map (CommRingCat.ofHom (algebraMap A Af)) ≫ y' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Spec_exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq.solution
