import Mathlib

import Theorems.Thm_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {k : ℕ} (r : Fin k → S)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (i j : Fin k) :
    ∃ fij : pullback (g i) (g j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j))),
      IsPullback (pullback.fst (g i) (g j)) fij (f' i)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight (r i) (r j) :
          Localization.Away (r i) →+* Localization.Away (r i * r j)))) ∧
      IsPullback (pullback.snd (g i) (g j)) fij (f' j)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft (r j) (r i) :
          Localization.Away (r j) →+* Localization.Away (r i * r j)))) := by
  have hcart := AlgebraicGeometry.isPullback_specMap_awayToAwayRight_awayToAwayLeft (r i) (r j)
  have wP : (pullback.fst (g i) (g j) ≫ f' i) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) =
      (pullback.snd (g i) (g j) ≫ f' j) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r j)))) := by
    rw [Category.assoc, ← (hg i).w, ← Category.assoc, pullback.condition, Category.assoc, (hg j).w, Category.assoc]
  refine ⟨hcart.lift _ _ wP, ?_, ?_⟩
  · have s := (IsPullback.of_hasPullback (g i) (g j)).paste_vert (hg j)
    rw [(hg i).w, ← hcart.lift_snd _ _ wP] at s
    exact s.of_bot (hcart.lift_fst _ _ wP).symm hcart
  · have s := (IsPullback.of_hasPullback (g i) (g j)).flip.paste_vert (hg i)
    rw [(hg j).w, ← hcart.lift_fst _ _ wP] at s
    exact s.of_bot (hcart.lift_snd _ _ wP).symm hcart.flip
