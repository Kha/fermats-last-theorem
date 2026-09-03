import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one

theorem GaloisRep.mem_ratLocalizedAt_iff_padic_norm_le_one
    (p : ℕ) [Fact p.Prime] (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ‖(q : ℚ_[p])‖ ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one.solution
