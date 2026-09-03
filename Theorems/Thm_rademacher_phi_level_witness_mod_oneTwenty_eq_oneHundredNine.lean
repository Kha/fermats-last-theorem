import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_mod_oneTwenty_eq_oneHundredNine

theorem rademacher_phi_level_witness_mod_oneTwenty_eq_oneHundredNine (j : ℕ) : 12 * ((((24 * j + 22 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((120 * j + 109 : ℕ) : ℚ)) / (12 * ((120 * j + 109 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (120 * j + 109)) = ((Nat.gcd ((120 * j + 109) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 4)) ∧ Nat.Coprime (Int.natAbs (-(4 * (j : ℤ) + 4))) (((120 * j + 109) - 1) / Nat.gcd ((120 * j + 109) - 1) 12) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_oneHundredNine.solution
