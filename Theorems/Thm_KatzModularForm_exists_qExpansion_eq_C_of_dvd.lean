import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import P2M.Util
import P2M.Sol.S_KatzModularForm_exists_qExpansion_eq_C_of_dvd

theorem KatzModularForm.exists_qExpansion_eq_C_of_dvd (m : ℕ) (c : ℤ)
    (hc : ((m / Nat.gcd m 12 : ℕ) : ℤ) ∣ c) :
    ∃ F : KatzModularForm (ZMod m) 2, F.qExpansion = HahnSeries.C (c : ZMod m) := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_exists_qExpansion_eq_C_of_dvd.solution
