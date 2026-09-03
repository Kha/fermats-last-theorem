import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
import P2M.Sol.S_W54_exists_galoisRepAdic_of_eigenPiece_tor

open Polynomial
open scoped TensorProduct
theorem W54.exists_galoisRepAdic_of_eigenPiece_tor
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ)
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
    [CharZero 𝒪'] (_hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    {M : Type} [AddCommGroup M] [Module 𝒪' M] [Module.Finite 𝒪' M] [Module.Free 𝒪' M]
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
    (TM : ModularCurve.HeckeAlg →+* Module.End 𝒪' M)
    (χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪')
    (hES :
      ∃ W : Submodule K (K ⊗[𝒪'] M),
        Module.finrank K W = 2 ∧
        ∃ hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W,
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ∀ w ∈ W,
            (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
              algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • w) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
              ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
                LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
                  algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) ∧
          (∀ (q : ℕ) (_ : q.Prime), q ≠ p → q ∣ N → ¬ q ^ 2 ∣ N →
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
              ∃ L : Submodule K (K ⊗[𝒪'] M),
                L ≤ W ∧ Module.finrank K L = 1 ∧
                ∃ a : K, a * a = 1 ∧
                  (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
                    ∀ w ∈ L, (ρM σ).baseChange K w = (a * (q : K)) • w) ∧
                  (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
                    ∀ w ∈ W, (ρM σ).baseChange K w - a • w ∈ L)))
    (hquad : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N) (_hℓS : ℓ ∉ S),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ∀ m : M, ρM σ (ρM σ m) - TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) (ρM σ m)
            + (ℓ : 𝒪') • m = 0)
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρM σ = 1)
    (hcont : GaloisActionIsAdicContinuous 𝒪' ρM) :
    ∃ ρ : GaloisRepAdic 𝒪',
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪'))) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → q ∣ N → ¬ q ^ 2 ∣ N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
            LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C ((q : 𝒪') + 1) * X + C ((q : 𝒪')) ∨
            LinearMap.charpoly (ρ.ρ σ) = X ^ 2 + C ((q : 𝒪') + 1) * X + C ((q : 𝒪'))) := by p2m_exact_reverting @_root_.P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_tor.solution
