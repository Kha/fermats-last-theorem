module

public import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_toricPoint_fst_coeff_of_not_dvd

@[expose] public section

open ModularCurve
theorem ModularCurve.toricPoint_fst_coeff_of_not_dvd (K : Type*) [Field K] (p : ℕ) (c : K) {m : ℕ} (hpm : ¬ p ∣ m) : (toricPoint K p c).1.coeff (m : ℤ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_toricPoint_fst_coeff_of_not_dvd.solution
