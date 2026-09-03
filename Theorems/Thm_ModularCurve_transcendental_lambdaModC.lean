import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import P2M.Util
import P2M.Sol.S_ModularCurve_transcendental_lambdaModC
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.transcendental_lambdaModC (K : Type*) [CommRing K] :
    Transcendental K (lambdaModC K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_transcendental_lambdaModC.solution
