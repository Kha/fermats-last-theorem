import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open Polynomial

theorem ResidualGaloisRep.exists_charpoly_eq_mul_of_isTaylorWilesPrime
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L₀] [IsGalois ℚ L₀]
    (b : Module.Basis (Fin 2) k ρbar.V) (ρmat : TaylorWiles.ResidualRep (↥L₀) k)
    (hρmat : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ) = LinearMap.toMatrix b b (ρbar.ρ σ))
    (p n q : ℕ) (htw : TaylorWiles.IsTaylorWilesPrime ρmat p n q) (hunr : ρbar.IsUnramifiedAt q) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
        ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime.solution
