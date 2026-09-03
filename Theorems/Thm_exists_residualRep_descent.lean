import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_exists_residualRep_descent
set_option autoImplicit false
theorem exists_residualRep_descent {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀]
    [NumberField L₀] [IsGalois ℚ L₀]
    (hker : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L₀, σ x = x) → ρbar.ρ σ = 1)
    (b : Module.Basis (Fin 2) k ρbar.V) :
    ∃ ρmat : TaylorWiles.ResidualRep (↥L₀) k,
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ)
          = LinearMap.toMatrix b b (ρbar.ρ σ) := by p2m_exact_reverting @_root_.P2MW.S_exists_residualRep_descent.solution
