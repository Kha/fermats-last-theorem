import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_fst_eq
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (L₁ L₂ : RelativeGroupLaw R' (pullback.snd f ι))
    (h₁ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
      (L₁.mul t' P Q).1 ≫ pullback.fst f ι =
        (G.mul (t' ≫ ι) ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (h₂ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
      (L₂.mul t' P Q).1 ≫ pullback.fst f ι =
        (G.mul (t' ≫ ι) ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    L₁ = L₂ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq.solution
