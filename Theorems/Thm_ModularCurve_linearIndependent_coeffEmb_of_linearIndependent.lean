import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent

set_option autoImplicit false

open ModularCurve

universe u v

theorem ModularCurve.linearIndependent_coeffEmb_of_linearIndependent
    (L : Type u) [Field L] [CharZero L]
    {ι : Type v} {v : ι → LaurentSeries ℚ} (hv : LinearIndependent ℚ v) :
    LinearIndependent L (fun i => coeffEmb L (v i)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent.solution
