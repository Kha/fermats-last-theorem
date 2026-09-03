import Mathlib
import P2M.Util
import P2M.Sol.S_QuotientGroup_eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange

universe u

theorem QuotientGroup.eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n s : ℕ)
    (ξ : (Fin s → Kˣ) ⧸ (Pi.constMonoidHom (Fin s) Kˣ).range) (hξ : ξ ^ (p ^ n) = 1) : ξ = 1 := by p2m_exact_reverting @_root_.P2MW.S_QuotientGroup_eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange.solution
