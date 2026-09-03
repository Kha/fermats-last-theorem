import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_PadicAlgCl_inertiaSubgroupIn_normal

set_option autoImplicit false

theorem PadicAlgCl.inertiaSubgroupIn_normal (p : ℕ) [Fact p.Prime] :
    ((padicIntegers p).inertiaSubgroupIn ℚ_[p] : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).Normal := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_inertiaSubgroupIn_normal.solution
