import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open ModularCurve CerednikDrinfeld

theorem CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_toricUniformization
    {p : ℕ} [Fact p.Prime] {M r₁ r₂ : ℕ} [Fact r₁.Prime] [Fact r₂.Prime] (hpr₁ : p ≠ r₁) (hpr₂ : p ≠ r₂)
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)} (hA₁ : A₁.LiesOverPrime r₁) (hA₂ : A₂.LiesOverPrime r₂)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t)
    (unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : T, p • t = 0 → gal σ t = t)
    (eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : T, p • t = 0 → gal σ (gal σ t) - hecke (heckeGen ⟨ℓ, hℓ⟩) (gal σ t) + ℓ • t = 0)
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal) :
    ∃ 𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂, 𝒥.Laws M r₁ r₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.solution
