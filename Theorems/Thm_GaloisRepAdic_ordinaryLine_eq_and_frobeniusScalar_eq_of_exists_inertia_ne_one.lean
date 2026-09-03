import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪]
    (ρ' : GaloisRepAdic 𝒪) (p : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ))

    (L : Submodule 𝒪 ρ'.V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 ρ'.V, L = 𝒪 ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ'.V, ρ'.ρ σ v - v ∈ L)
    (α : 𝒪)
    (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p →
      ∀ v : ρ'.V, ρ'.ρ σ v - α • v ∈ L)

    (L' : Submodule 𝒪 ρ'.V)
    (hL'b : ∃ b : Module.Basis (Fin 2) 𝒪 ρ'.V, L' = 𝒪 ∙ b 0)
    (hL'I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ'.V, ρ'.ρ τ v - v ∈ L')
    (α' : 𝒪)
    (hα' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
      ∀ v : ρ'.V, ρ'.ρ σ v - α' • v ∈ L')

    (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ'.ρ τ ≠ 1) :
    L = L' ∧
      ((∃ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p) → α = α') := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one.solution
