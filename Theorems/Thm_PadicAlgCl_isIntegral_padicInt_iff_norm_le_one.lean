import Mathlib
import P2M.Util
import P2M.Sol.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one

set_option autoImplicit false

theorem PadicAlgCl.isIntegral_padicInt_iff_norm_le_one (p : ℕ) [Fact p.Prime]
    (x : PadicAlgCl p) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one.solution
