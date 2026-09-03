import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_blrBlock_of_frobeniusQuadratic_of_dense

theorem ModularCurve.exists_blrBlock_of_frobeniusQuadratic_of_dense {J : Type*} [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ModularCurve.HeckeAlg ⧸ 𝔪))
    (hirr : ∀ (W : Submodule (ModularCurve.HeckeAlg ⧸ 𝔪) (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪)),
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1)
    (h2 : (2 : ModularCurve.HeckeAlg ⧸ 𝔪) ≠ 0)
    (hES : ModularCurve.FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧ Ideal.Quotient.mk 𝔪 ((ℓ : ModularCurve.HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ModularCurve.heckeTorsion J 𝔪 : Set J)))
    (hne : ModularCurve.heckeTorsion J 𝔪 ≠ ⊥) :
    ∃ ι : (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪) →+ J, Function.Injective ι ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪), ι ((ρ σ).mulVec v) = σ • ι v) ∧
      ∀ (v : Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪), ι v ∈ ModularCurve.heckeTorsion J 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_blrBlock_of_frobeniusQuadratic_of_dense.solution
