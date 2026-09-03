import Definitions.Def_TateCurve_QSeries
import P2M.Util
import P2M.Sol.S_TateCurve_nnnorm_twistParam_curve_eq_one

open TateCurve NNReal
open scoped NNReal
namespace TateCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
theorem nnnorm_twistParam_curve_eq_one (E : WeierstrassCurve K)
    (hc₄ : ‖E.c₄‖₊ = 1) (hΔ : ‖E.Δ‖₊ < 1) {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    ‖E.c₆ * (curve q).c₄ / ((curve q).c₆ * E.c₄)‖₊ = 1 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_nnnorm_twistParam_curve_eq_one.solution
end TateCurve
