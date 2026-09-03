import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.exists_isPullback_fst_toSpecAway_of_charts_of_isPullback
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (i j : Fin k) :
    ∃ (ρ₁ : B i →ₐ[S] Localization.Away (r i * r j))
      (fP : Limits.pullback (ι i) (ι j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j)))),
      (letI := ρ₁.toRingHom.toAlgebra
       IsLocalization.Away (algebraMap S (B i) (r j)) (Localization.Away (r i * r j))) ∧
      CategoryTheory.IsPullback (Limits.pullback.fst (ι i) (ι j)) fP (f' i) (Spec.map (CommRingCat.ofHom ρ₁.toRingHom)) ∧
      fP ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) =
        Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback.solution
