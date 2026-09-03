import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eval_PsiSq_variableChange

theorem WeierstrassCurve.eval_PsiSq_variableChange {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (n : ℤ) (x : R) :
    ((C • W).ΨSq n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * (n.natAbs ^ 2 - 1)) * (W.ΨSq n).eval x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eval_PsiSq_variableChange.solution
