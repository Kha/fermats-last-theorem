import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent
    (C : Type) [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    {X Y₀ : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of C))
    (q₀ : Y₀ ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) [Etale q₀] :
    ∃ (Y : Scheme.{0}) (q : Y ⟶ X) (_ : Etale q) (j : Y₀ ⟶ Y)
      (_ : IsPullback j q₀ q (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      ∀ (B : Type) [CommRing B] [Algebra C B] (t : Spec (CommRingCat.of B) ⟶ X),
        t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap C B)) →
        ∀ (s₀ : Spec (CommRingCat.of (B ⧸ J.map (algebraMap C B))) ⟶ Y₀),
          s₀ ≫ q₀ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ t →
          ∃! s : Spec (CommRingCat.of B) ⟶ Y, s ≫ q = t ∧
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ s = s₀ ≫ j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent.solution
