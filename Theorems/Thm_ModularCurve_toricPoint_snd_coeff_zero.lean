import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_toricPoint_snd_coeff_zero

open ModularCurve
theorem ModularCurve.toricPoint_snd_coeff_zero (K : Type*) [Field K] (p : ℕ) (c : K) : (toricPoint K p c).2.coeff 0 = c ^ 2 / (1 - c) ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_toricPoint_snd_coeff_zero.solution
