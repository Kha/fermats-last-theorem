import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_five

theorem rademacher_phi_level_witness_five (j : ℕ) : 12 * ((((4 * j + 2 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 5 : ℕ) : ℚ)) / (12 * ((12 * j + 5 : ℕ) : ℚ)) + dedekindSum 3 1 - dedekindSum 3 (12 * j + 5)) = ((Nat.gcd ((12 * j + 5) - 1) 12 : ℕ) : ℚ) * (-(2 * (j : ℤ) + 1)) ∧ Nat.Coprime (Int.natAbs (-(2 * (j : ℤ) + 1))) (((12 * j + 5) - 1) / Nat.gcd ((12 * j + 5) - 1) 12) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_five.solution
