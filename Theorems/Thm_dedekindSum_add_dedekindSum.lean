import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_dedekindSum_add_dedekindSum

theorem dedekindSum_add_dedekindSum (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k) : dedekindSum h k + dedekindSum k h = ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 := by p2m_exact_reverting @_root_.P2MW.S_dedekindSum_add_dedekindSum.solution
