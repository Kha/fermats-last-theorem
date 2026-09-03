import Theorems.Thm_TaylorWiles_exists_isTaylorWilesPrime
import Theorems.Thm_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_seed
attribute [-instance] FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open Polynomial

theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L₀] [IsGalois ℚ L₀]
    (b : Module.Basis (Fin 2) k ρbar.V) (ρmat : TaylorWiles.ResidualRep (↥L₀) k)
    (hρmat : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ) = LinearMap.toMatrix b b (ρbar.ρ σ))
    (p n : ℕ) {S : Finset ℕ} (seed : TaylorWiles.Seed ρmat p n S) (B : Finset ℕ)
    (hunr : ∀ q : ℕ, q.Prime → q ∉ B → ρbar.IsUnramifiedAt q) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ∉ B ∧ q ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by
  obtain ⟨q, hqS, hqB, htw⟩ := TaylorWiles.exists_isTaylorWilesPrime ρmat p n seed B
  exact ⟨q, htw.1, hqS, hqB, htw.2.1, hunr q htw.1 hqB,
    ResidualGaloisRep.exists_charpoly_eq_mul_of_isTaylorWilesPrime ρbar L₀ b ρmat hρmat p n q htw
      (hunr q htw.1 hqB)⟩
