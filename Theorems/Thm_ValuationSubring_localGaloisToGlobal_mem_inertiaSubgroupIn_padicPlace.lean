import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_ValuationSubring_localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace

set_option autoImplicit false
theorem ValuationSubring.localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace (p : ℕ) [Fact p.Prime]
    (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (hτ : τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) :
    localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace.solution
