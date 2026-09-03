import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible_univ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u
theorem GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible_univ
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (S₁ S₂ : Type u) [CommRing S₁] [CommRing S₂] [Algebra S S₁] [Algebra S S₂]
    (φ : S₁ →+* S₂) (hφ : φ.comp (algebraMap S S₁) = algebraMap S S₂)
    (L₁ : RelativeGroupLaw S₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))))
    (L₂ : RelativeGroupLaw S₂ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₂)))))
    (h₁ : (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₁))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
          (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (h₂ : (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))))),
          (L₂.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₂)))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (ρ : Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ⟶
          Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
    (hρ₁ : ρ ≫ pullback.fst _ _ = pullback.fst _ _)
    (hρ₂ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ)) :
    ρ ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁ =
      negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₂)))) L₂ ≫ ρ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible_univ.solution
