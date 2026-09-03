import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_witness_mod_sixty_eq_thirtySeven

theorem rademacher_phi_level_witness_mod_sixty_eq_thirtySeven (i : ℕ) : 12 * ((((24 * i + 15 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((60 * i + 37 : ℕ) : ℚ)) / (12 * ((60 * i + 37 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (60 * i + 37)) = ((Nat.gcd ((60 * i + 37) - 1) 12 : ℕ) : ℚ) * (-(3 * (i : ℤ) + 2)) ∧ Nat.Coprime (Int.natAbs (-(3 * (i : ℤ) + 2))) (((60 * i + 37) - 1) / Nat.gcd ((60 * i + 37) - 1) 12) := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_witness_mod_sixty_eq_thirtySeven.solution
