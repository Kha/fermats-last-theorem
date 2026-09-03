import Definitions.Def_TateCurve_QSeries
import P2M.Util
import P2M.Sol.S_TateCurve_nnnorm_Delta

open TateCurve NNReal
open scoped NNReal
namespace TateCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K}
theorem nnnorm_Delta (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : ‖(curve q).Δ‖₊ = ‖q‖₊ := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_nnnorm_Delta.solution
end TateCurve
