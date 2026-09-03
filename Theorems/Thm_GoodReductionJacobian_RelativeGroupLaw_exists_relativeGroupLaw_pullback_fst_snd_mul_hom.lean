import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_pullback_fst_snd_mul_hom
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) :
    ∃ LP : RelativeGroupLaw R (pullback.fst f f ≫ f),

      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ pullback.fst f f =
            (L.mul t ⟨P.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact P.2⟩
              ⟨Q.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact Q.2⟩).1) ∧
      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ pullback.snd f f =
            (L.mul t ⟨P.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]; exact P.2⟩
              ⟨Q.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]; exact Q.2⟩).1) ∧

      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)),
          (LP.one t).1 ≫ pullback.fst f f = (L.one t).1 ∧ (LP.one t).1 ≫ pullback.snd f f = (L.one t).1) ∧

      (L.IsCommutative →
        ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 =
            (L.mul t
              ⟨P.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
                by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact P.2⟩
              ⟨Q.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
                by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact Q.2⟩).1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.solution
