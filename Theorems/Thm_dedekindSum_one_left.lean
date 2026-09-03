import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_dedekindSum_one_left

theorem dedekindSum_one_left (k : ℕ) : dedekindSum 1 k = ((k : ℚ) - 1) * ((k : ℚ) - 2) / (12 * k) := by p2m_exact_reverting @_root_.P2MW.S_dedekindSum_one_left.solution
