import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_mod_sixty_eq_thirteen

theorem rademacher_phi_level_witness_mod_sixty_eq_thirteen (i : ℕ) : 12 * ((((36 * i + 8 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((60 * i + 13 : ℕ) : ℚ)) / (12 * ((60 * i + 13 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (60 * i + 13)) = ((Nat.gcd ((60 * i + 13) - 1) 12 : ℕ) : ℚ) * (-(4 * (i : ℤ) + 1)) ∧ Nat.Coprime (Int.natAbs (-(4 * (i : ℤ) + 1))) (((60 * i + 13) - 1) / Nat.gcd ((60 * i + 13) - 1) 12) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_mod_sixty_eq_thirteen.solution
