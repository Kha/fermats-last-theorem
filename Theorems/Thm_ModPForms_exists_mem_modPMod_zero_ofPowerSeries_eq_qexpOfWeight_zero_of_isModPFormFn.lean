import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import P2M.Util
import P2M.Sol.S_ModPForms_exists_mem_modPMod_zero_ofPowerSeries_eq_qexpOfWeight_zero_of_isModPFormFn
set_option autoImplicit false
open ModularCurve

theorem ModPForms.exists_mem_modPMod_zero_ofPowerSeries_eq_qexpOfWeight_zero_of_isModPFormFn
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p]
    (G : ↥(modularFunctionFieldC K N)) (hG : IsModPFormFn K 0 (G : LaurentSeries K)) :
    ∃ φ : PowerSeries K, φ ∈ ModPForms.modPMod N (2 * ((0 : ℕ) : ℤ)) K ∧
      HahnSeries.ofPowerSeries ℤ K φ = qexpOfWeight K ((0 : ℕ) : ℤ) (G : LaurentSeries K) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_exists_mem_modPMod_zero_ofPowerSeries_eq_qexpOfWeight_zero_of_isModPFormFn.solution
