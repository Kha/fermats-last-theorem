import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    {Z₁ Z₂ : Scheme.{0}} (ι₁ : Z₁ ⟶ A) (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₁] [IsClosedImmersion ι₂]
    (𝔭 : PrimeSpectrum S)
    (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)))
    (V : A.affineOpens) (Bₚ : Type) [CommRing Bₚ] [Algebra Γ(A, V.1) Bₚ]
    [IsLocalization (𝔭.asIdeal.primeCompl.map
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ V.1 le_top).hom.toMonoidHom) Bₚ] :
    (ι₁.ker.ideal V).map (algebraMap Γ(A, V.1) Bₚ) = (ι₂.ker.ideal V).map (algebraMap Γ(A, V.1) Bₚ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime.solution
