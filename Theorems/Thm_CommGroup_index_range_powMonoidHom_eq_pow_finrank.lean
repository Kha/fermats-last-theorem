import Mathlib
import P2M.Util
import P2M.Sol.S_CommGroup_index_range_powMonoidHom_eq_pow_finrank

set_option autoImplicit false
theorem CommGroup.index_range_powMonoidHom_eq_pow_finrank {F : Type*} [CommGroup F] [Group.FG F]
    (htf : ∀ (x : F) (m : ℕ), 0 < m → x ^ m = 1 → x = 1) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : F →* F).range.index = n ^ Module.finrank ℤ (Additive F) := by p2m_exact_reverting @_root_.P2MW.S_CommGroup_index_range_powMonoidHom_eq_pow_finrank.solution
