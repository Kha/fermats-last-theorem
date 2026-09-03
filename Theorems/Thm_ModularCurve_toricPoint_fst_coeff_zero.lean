import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_toricPoint_fst_coeff_zero

open ModularCurve
theorem ModularCurve.toricPoint_fst_coeff_zero (K : Type*) [Field K] (p : ℕ) (c : K) : (toricPoint K p c).1.coeff 0 = c / (1 - c) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_toricPoint_fst_coeff_zero.solution
