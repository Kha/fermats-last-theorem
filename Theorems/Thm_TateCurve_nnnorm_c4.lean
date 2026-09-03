import Definitions.Def_TateCurve_QSeries
import P2M.Util
import P2M.Sol.S_TateCurve_nnnorm_c4

open TateCurve NNReal
open scoped NNReal
namespace TateCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K}
theorem nnnorm_c4 (hq : ‖q‖₊ < 1) : ‖(curve q).c₄‖₊ = 1 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_nnnorm_c4.solution
end TateCurve
