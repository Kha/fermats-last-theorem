import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.IsModPFormFn.of_coeffMap_algebraMap
    {K₀ K : Type*} [Field K₀] [Field K] [Algebra K₀ K] [Algebra.IsAlgebraic K₀ K]
    (m : ℕ) (G : LaurentSeries K₀)
    (hG : IsModPFormFn K m (ModularCurve.coeffMap (algebraMap K₀ K) G)) :
    IsModPFormFn K₀ m G := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap.solution
