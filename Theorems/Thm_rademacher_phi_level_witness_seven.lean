import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_seven

theorem rademacher_phi_level_witness_seven (j : ℕ) : 12 * ((((3 * j + 2 : ℕ) + 4 : ℤ) : ℚ) * (1 - ((12 * j + 7 : ℕ) : ℚ)) / (12 * ((12 * j + 7 : ℕ) : ℚ)) + dedekindSum 4 1 - dedekindSum 4 (12 * j + 7)) = ((Nat.gcd ((12 * j + 7) - 1) 12 : ℕ) : ℚ) * (-((j : ℤ) + 1)) ∧ Nat.Coprime (Int.natAbs (-((j : ℤ) + 1))) (((12 * j + 7) - 1) / Nat.gcd ((12 * j + 7) - 1) 12) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_seven.solution
