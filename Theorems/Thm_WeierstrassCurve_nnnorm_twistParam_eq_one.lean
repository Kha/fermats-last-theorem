import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Tactic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_nnnorm_twistParam_eq_one
attribute [-simp] TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃

open scoped NNReal
namespace WeierstrassCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
theorem nnnorm_twistParam_eq_one (E E' : WeierstrassCurve K)
    (hc₄ : ‖E.c₄‖₊ = 1) (hΔ : ‖E.Δ‖₊ < 1) (hc₄' : ‖E'.c₄‖₊ = 1) (hΔ' : ‖E'.Δ‖₊ < 1) :
    ‖E.c₆ * E'.c₄ / (E'.c₆ * E.c₄)‖₊ = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_nnnorm_twistParam_eq_one.solution
end WeierstrassCurve
