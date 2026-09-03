import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft
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
          Localization.Away (r j) →+* Localization.Away (r i * r j)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft.solution
