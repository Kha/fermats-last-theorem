import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne

theorem rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne (j : ℕ) : 12 * ((((45 * j + 23 : ℕ) + 8 : ℤ) : ℚ) * (1 - ((120 * j + 61 : ℕ) : ℚ)) / (12 * ((120 * j + 61 : ℕ) : ℚ)) + dedekindSum 8 1 - dedekindSum 8 (120 * j + 61)) = ((Nat.gcd ((120 * j + 61) - 1) 12 : ℕ) : ℚ) * (-(5 * (j : ℤ) + 3)) ∧ Nat.Coprime (Int.natAbs (-(5 * (j : ℤ) + 3))) (((120 * j + 61) - 1) / Nat.gcd ((120 * j + 61) - 1) 12) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne.solution
