import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_dedekindSum_natCast_sub_one

theorem dedekindSum_natCast_sub_one (k : ℕ) : dedekindSum ((k : ℤ) - 1) k = -dedekindSum 1 k := by p2m_exact_reverting @_root_.P2MW.S_dedekindSum_natCast_sub_one.solution
