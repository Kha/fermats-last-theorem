import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_IsModPFormFn_coeffMap
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.IsModPFormFn.coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (ι : K₀ →+* K) (m : ℕ) (G : LaurentSeries K₀)
    (hG : IsModPFormFn K₀ m G) :
    IsModPFormFn K m (ModularCurve.coeffMap ι G) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsModPFormFn_coeffMap.solution
