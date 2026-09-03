import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
    (p : ℕ) [Fact p.Prime] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ (padicPlace p).inertiaSubgroupIn ℚ) :
    ∃ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧ localGaloisToGlobal p τ = σ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq.solution
