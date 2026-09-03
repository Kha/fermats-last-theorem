import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one

set_option autoImplicit false

open scoped TensorProduct
theorem PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
    (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔
      ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one.solution
