import Mathlib
import P2M.Util
import P2M.Sol.S_Padic_natCard_units_quot_range_powMonoidHom_of_ne_two

theorem Padic.natCard_units_quot_range_powMonoidHom_of_ne_two {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) :
    Nat.card ((ℚ_[p])ˣ ⧸ (powMonoidHom p : (ℚ_[p])ˣ →* (ℚ_[p])ˣ).range) = p ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_Padic_natCard_units_quot_range_powMonoidHom_of_ne_two.solution
