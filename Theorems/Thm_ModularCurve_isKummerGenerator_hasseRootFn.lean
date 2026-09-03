import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import P2M.Util
import P2M.Sol.S_ModularCurve_isKummerGenerator_hasseRootFn
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

theorem ModularCurve.isKummerGenerator_hasseRootFn
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (w : ModularCurve.IntegralWeightOneForm κ M) :
    ModularCurve.IgusaCover.IsKummerGenerator (p - 1) (ModularCurve.x1FunctionFieldC κ M) w.hasseRootFn := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isKummerGenerator_hasseRootFn.solution
