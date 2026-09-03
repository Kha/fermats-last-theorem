import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap
attribute [-simp] ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

theorem ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (h : ∃ (k' : Type) (_ : Field k') (ψk : k →+* k')
        (b : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψk).V)
        (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (ρ.baseChangeAlong ψk).ρ σ (b 0) = ψ σ • b 0 ∧
            (ρ.baseChangeAlong ψk).ρ σ (b 1) = ψ' σ • b 1) ∧
        (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀) ∧
        (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
            (ρ.baseChangeAlong ψk).ρ φ₀ (b 0) ∈ Submodule.span k' {b 1})) :
    ∀ (k'' : Type) [Field k''] (ψ'' : k →+* k''),
      ∀ L : Submodule k'' (ρ.baseChangeAlong ψ'').V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, (ρ.baseChangeAlong ψ'').ρ σ v ∈ L) →
        L = ⊥ ∨ L = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap.solution
