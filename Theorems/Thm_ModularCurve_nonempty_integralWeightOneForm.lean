import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import P2M.Util
import P2M.Sol.S_ModularCurve_nonempty_integralWeightOneForm
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

theorem ModularCurve.nonempty_integralWeightOneForm
    (κ : Type) [Field κ] (M : ℕ) (hM : 3 ≤ M) :
    Nonempty (ModularCurve.IntegralWeightOneForm κ M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nonempty_integralWeightOneForm.solution
