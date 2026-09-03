import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import P2M.Util
import P2M.Sol.S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod

namespace FreyCurve
open WeierstrassCurve
theorem eight_mul_Psi2Sq_eval_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (x : ZMod q) :
    8 * (((FreyPackage.freyCurveInt P).reductionMod q).Ψ₂Sq.eval x) =
      2 * x * (4 * x - ((P.a : ZMod q)) ^ P.p) * (4 * x + ((P.b : ZMod q)) ^ P.p) := by p2m_exact_reverting @_root_.P2MW.S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod.solution
end FreyCurve
