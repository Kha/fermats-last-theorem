import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import P2M.Util
import P2M.Sol.S_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three

open Polynomial
theorem PadicInt.exists_pow_eq_of_exists_pow_eq_toZModPow_three {p : ℕ} [hp : Fact p.Prime] {u : ℤ_[p]} (hu : ‖u‖ = 1) (hres : ∃ c : ZMod (p ^ 3), c ^ p = PadicInt.toZModPow 3 u) :
    ∃ z : ℤ_[p], z ^ p = u := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three.solution
