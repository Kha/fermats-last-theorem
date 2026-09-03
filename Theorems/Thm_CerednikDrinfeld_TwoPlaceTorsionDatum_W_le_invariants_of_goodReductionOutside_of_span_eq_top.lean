import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open ModularCurve hiding exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense open CerednikDrinfeld

theorem CerednikDrinfeld.TwoPlaceTorsionDatum.W_le_invariants_of_goodReductionOutside_of_span_eq_top
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    {M : ℕ} (hgood : 𝒥.fst.GoodReductionOutside M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    (F : Type) [Field F] [Fintype F] (ι : F →+* HeckeAlg ⧸ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (hatt : ∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
          Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
            Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det)
    (hspan : Submodule.span (HeckeAlg ⧸ 𝔪)
      (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => (ρ σ).map ι) = ⊤)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hunr : ∀ σ ∈ A₂.inertiaSubgroupIn ℚ, ρ σ = 1) :
    𝒥.snd.W 𝔪 ≤ 𝒥.snd.invariants := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top.solution
