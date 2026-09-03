import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_mod_oneTwenty_eq_one

theorem rademacher_phi_level_witness_mod_oneTwenty_eq_one (w t : ℕ) : 12 * (((-((60 * 2 ^ w * (2 * t + 1) + 15 * t + 8 : ℕ) : ℤ) + 2 ^ (w + 4) : ℤ) : ℚ) * (1 - ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℚ)) / (12 * ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℚ)) + dedekindSum (2 ^ (w + 4)) 1 - dedekindSum (2 ^ (w + 4)) (120 * 2 ^ w * (2 * t + 1) + 1)) = ((Nat.gcd ((120 * 2 ^ w * (2 * t + 1) + 1) - 1) 12 : ℕ) : ℚ) * (2 ^ (w + 1) * (5 * (t : ℤ) + 2)) ∧ Nat.Coprime (5 * t + 2) (5 * (2 * t + 1)) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_one.solution
