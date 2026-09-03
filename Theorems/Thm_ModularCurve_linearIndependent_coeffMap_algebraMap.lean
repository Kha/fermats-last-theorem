import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_linearIndependent_coeffMap_algebraMap

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.linearIndependent_coeffMap_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    {ι : Type*} (v : ι → LaurentSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => coeffMap (algebraMap K L) (v i)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_linearIndependent_coeffMap_algebraMap.solution
