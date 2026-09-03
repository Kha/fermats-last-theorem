import Mathlib
import Theorems.Thm_Padic_index_range_powMonoidHom_units_of_ne_two
import P2M.Util
namespace P2MW.S_Padic_natCard_units_quot_range_powMonoidHom_of_ne_two

open Polynomial

theorem solution {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) :
    Nat.card ((ℚ_[p])ˣ ⧸ (powMonoidHom p : (ℚ_[p])ˣ →* (ℚ_[p])ˣ).range) = p ^ 2 := by
  rw [← Subgroup.index_eq_card]
  exact Padic.index_range_powMonoidHom_units_of_ne_two hp2
