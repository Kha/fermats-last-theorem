import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_eleven

theorem rademacher_phi_level_witness_eleven (j : ℕ) : 12 * ((((4 * j + 4 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 11 : ℕ) : ℚ)) / (12 * ((12 * j + 11 : ℕ) : ℚ)) + dedekindSum 3 1 - dedekindSum 3 (12 * j + 11)) = ((Nat.gcd ((12 * j + 11) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 4)) ∧ Nat.Coprime (Int.natAbs (-(4 * (j : ℤ) + 4))) (((12 * j + 11) - 1) / Nat.gcd ((12 * j + 11) - 1) 12) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_eleven.solution
