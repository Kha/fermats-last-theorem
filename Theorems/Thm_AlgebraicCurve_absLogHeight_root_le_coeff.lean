import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_absLogHeight_root_le_coeff

theorem AlgebraicCurve.absLogHeight_root_le_coeff {p : Polynomial (AlgebraicClosure ℚ)}
    (hmonic : p.Monic) {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_absLogHeight_root_le_coeff.solution
