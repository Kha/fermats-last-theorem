import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_deg_qInftyPlaceRat
import P2M.Util
namespace P2MW.S_ModularCurve_deg_cuspInftyFull

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N] : (cuspInftyFull N).deg = 1 :=
  ModularCurve.deg_qInftyPlaceRat _
