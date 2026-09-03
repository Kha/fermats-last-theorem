import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) [IsProper f]
    {Z₁ Z₂ : Scheme.{0}} (ι₁ : Z₁ ⟶ A) (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₁] [IsClosedImmersion ι₂]
    (𝔭 : PrimeSpectrum S)
    (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ))) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.Away g)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper.solution
