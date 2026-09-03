import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_inertia_diagonal_swap_of_eigenvector

theorem ResidualGaloisRep.exists_inertia_diagonal_swap_of_eigenvector
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (h : ∃ (k' : Type) (_ : Field k') (ψk : k →+* k') (v : (ρ.baseChangeAlong ψk).V)
        (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        v ≠ 0 ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, (ρ.baseChangeAlong ψk).ρ σ v = χ σ • v) ∧
        (∃ φ ∈ P.decompositionSubgroup ℚ, ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, χ (φ⁻¹ * σ₀ * φ) ≠ χ σ₀)) :
    ∃ (k' : Type) (_ : Field k') (ψk : k →+* k')
        (b : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψk).V)
        (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (ρ.baseChangeAlong ψk).ρ σ (b 0) = ψ σ • b 0 ∧
            (ρ.baseChangeAlong ψk).ρ σ (b 1) = ψ' σ • b 1) ∧
        (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀) ∧
        (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
            (ρ.baseChangeAlong ψk).ρ φ₀ (b 0) ∈ Submodule.span k' {b 1}) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_inertia_diagonal_swap_of_eigenvector.solution
