import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import P2M.Util
import P2M.Sol.S_ModularCurve_isModPFormFn_zero_and_add_and_smul

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.isModPFormFn_zero_and_add_and_smul (K : Type*) [Field K] (m : ℕ) :
    IsModPFormFn K m 0 ∧
      (∀ G H : LaurentSeries K, IsModPFormFn K m G → IsModPFormFn K m H → IsModPFormFn K m (G + H)) ∧
      (∀ (c : K) (G : LaurentSeries K), IsModPFormFn K m G → IsModPFormFn K m (c • G)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isModPFormFn_zero_and_add_and_smul.solution
