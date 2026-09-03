import Mathlib
import P2M.Util
import P2M.Sol.S_RatFunc_trdeg_eq_one

universe u

theorem RatFunc.trdeg_eq_one (K : Type u) [Field K] : Algebra.trdeg K (RatFunc K) = 1 := by p2m_exact_reverting @_root_.P2MW.S_RatFunc_trdeg_eq_one.solution
