import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eval_prePsi_variableChange

theorem WeierstrassCurve.eval_prePsi_variableChange {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (n : ℤ) (x : R) :
    ((C • W).preΨ n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ (n.natAbs ^ 2 - if Even n then 4 else 1) * (W.preΨ n).eval x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eval_prePsi_variableChange.solution
