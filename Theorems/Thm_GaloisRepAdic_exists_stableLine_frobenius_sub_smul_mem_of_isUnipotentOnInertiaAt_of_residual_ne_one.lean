import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one

set_option autoImplicit false

theorem GaloisRepAdic.exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one
    {A : Type} [CommRing A] [IsLocalRing A] [IsReduced A]
    (ρ : GaloisRepAdic A) (q : ℕ) (hunip : ρ.IsUnipotentOnInertiaAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ₀ : τ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hτ₀' : ρ.residual.ρ τ₀ ≠ 1) :
    ∃ (L : Submodule A ρ.V) (u : A),
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) = L ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v ∈ L, ρ.ρ τ v = v) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρ.V, ρ.ρ σ v - u • v ∈ L) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one.solution
