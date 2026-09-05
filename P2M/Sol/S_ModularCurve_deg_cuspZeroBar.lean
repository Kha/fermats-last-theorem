import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_ModularCurve_deg_cuspInftyBar
import P2M.Util
namespace P2MW.S_ModularCurve_deg_cuspZeroBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    (cuspZeroBar N).deg = 1 := by
  rw [cuspZeroBar_def, Place.deg_smul]
  exact ModularCurve.deg_cuspInftyBar N
