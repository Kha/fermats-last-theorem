import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine

theorem rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine (j : ℕ) : 12 * ((((24 * j + 10 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((120 * j + 49 : ℕ) : ℚ)) / (12 * ((120 * j + 49 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (120 * j + 49)) = ((Nat.gcd ((120 * j + 49) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 2)) ∧ Nat.Coprime (2 * j + 1) (10 * j + 4) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine.solution
