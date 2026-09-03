import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hΓ : ∀ i, Function.Surjective ((f' i).appTop).hom ∧
      ∀ r : B i, Function.Surjective
        ((pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (B i) (Localization.Away r))))).appTop).hom)
    (e : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A' i) (he : ∀ i, e i ≫ f' i = 𝟙 _)
    (heagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
        (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
        Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ e i ≫ ι i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ e j ≫ ι j) :
    ∃ (ρ₁ : ∀ i j : Fin k, B i →ₐ[S] Localization.Away (r i * r j))
      (ρ₂ : ∀ i j : Fin k, B j →ₐ[S] Localization.Away (r i * r j))
      (fP : ∀ i j : Fin k,
        Limits.pullback (ι i) (ι j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j))))
      (eP : ∀ i j : Fin k,
        Spec (CommRingCat.of (Localization.Away (r i * r j))) ⟶ Limits.pullback (ι i) (ι j)),

      (∀ i j, eP i j ≫ fP i j = 𝟙 _) ∧
      (∀ i j, fP i j ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) =
        Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ∧
      (∀ i j, eP i j ≫ Limits.pullback.fst (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom) ≫ e i) ∧
      (∀ i j, eP i j ≫ Limits.pullback.snd (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom) ≫ e j) ∧
      (∀ i j, Function.Surjective ((fP i j).appTop).hom) ∧
      (∀ (i j : Fin k) (r' : Localization.Away (r i * r j)), Function.Surjective
        ((pullback.snd (fP i j) (Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.Away (r i * r j)) (Localization.Away r'))))).appTop).hom) ∧

      (∀ (i j l : Fin k)
        (π₁₃ : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶
          Limits.pullback (ι i) (ι l))
        (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) =
          (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫
            Limits.pullback.fst (ι i) (ι j))
        (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) =
          (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫
            Limits.pullback.snd (ι j) (ι l)),
        ∃ (fT : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶
              Spec (CommRingCat.of (Localization.Away (r i * r j * r l))))
          (eT : Spec (CommRingCat.of (Localization.Away (r i * r j * r l))) ⟶
              Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)))
          (σ₁₂ : Localization.Away (r i * r j) →ₐ[S] Localization.Away (r i * r j * r l))
          (σ₂₃ : Localization.Away (r j * r l) →ₐ[S] Localization.Away (r i * r j * r l))
          (σ₁₃ : Localization.Away (r i * r l) →ₐ[S] Localization.Away (r i * r j * r l)),
          eT ≫ fT = 𝟙 _ ∧ Function.Surjective (fT.appTop).hom ∧
          eT ≫ Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) =
            Spec.map (CommRingCat.ofHom σ₁₂.toRingHom) ≫ eP i j ∧
          eT ≫ Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) =
            Spec.map (CommRingCat.ofHom σ₂₃.toRingHom) ≫ eP j l ∧
          eT ≫ π₁₃ = Spec.map (CommRingCat.ofHom σ₁₃.toRingHom) ≫ eP i l) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop.solution
