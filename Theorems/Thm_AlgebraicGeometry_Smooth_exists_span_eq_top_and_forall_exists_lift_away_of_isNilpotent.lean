import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [Smooth f]
    {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    (t : Spec (CommRingCat.of C) ⟶ S) (x₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ t) :
    ∃ (ι : Type u) (a : ι → C), Ideal.span (Set.range a) = ⊤ ∧
      ∀ i : ι, ∃ x : Spec (CommRingCat.of (Localization.Away (a i))) ⟶ X,
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫ t ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J.map (algebraMap C (Localization.Away (a i))))))) ≫ x =
          Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map (algebraMap C (Localization.Away (a i))))
            (algebraMap C (Localization.Away (a i))) Ideal.le_comap_map)) ≫ x₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent.solution
