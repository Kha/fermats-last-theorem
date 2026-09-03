import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_exists_intCast_eq_six_mul_dedekindSum

theorem exists_intCast_eq_six_mul_dedekindSum (h k : ℕ) (hk : 0 < k) : ∃ z : ℤ, (z : ℚ) = 6 * k * dedekindSum h k := by p2m_exact_reverting @_root_.P2MW.S_exists_intCast_eq_six_mul_dedekindSum.solution
