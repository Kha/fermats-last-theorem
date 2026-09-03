import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_Padic_forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one

open scoped NNReal

theorem Padic.forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (d : ℚ_[p]) (hd : ‖d‖₊ = 1)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d) :
    ∀ τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → τ s = s := by p2m_exact_reverting @_root_.P2MW.S_Padic_forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one.solution
