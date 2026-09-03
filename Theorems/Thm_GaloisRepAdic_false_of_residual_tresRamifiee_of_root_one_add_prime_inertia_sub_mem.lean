import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem

set_option autoImplicit false
theorem GaloisRepAdic.false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem
    {B : Type} [CommRing B] [IsLocalRing B] (p : ℕ) [Fact p.Prime] (ρ : GaloisRepAdic B)
    (β : PadicAlgCl p) (hβ : β ^ p = 1 + (p : PadicAlgCl p))
    (hsplit : ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ) → τ β = β →
          ∀ v : ρ.V, ρ.ρ (localGaloisToGlobal p τ) v - v ∈
            (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V))
    (htres : ∀ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
        (∀ i, (padicPlace p).valuation (u i) = 1) →
        (∀ i, ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, σ (u i) = u i) →
        (∀ i, β i ^ p = u i) →
        ∃ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) ∧ (∀ i, σ (β i) = β i) ∧
            ρ.residual.ρ σ ≠ 1) :
    False := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem.solution
