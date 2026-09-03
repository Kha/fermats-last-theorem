import Definitions.Def_TateCurve_XMultSeparation
import Theorems.Thm_TateCurve_symAdd_sum_allParams_unconditional
import Theorems.Thm_TateCurve_diffHyp_unconditional
import P2M.Util
namespace P2MW.S_TateCurve_symAddHyps_unconditional

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    SymAddHyps q := by
  have hqR : ‖q‖ < 1 := by exact_mod_cast hq
  exact symAddHyps_of_sum_diff_of_isAlgClosed hq0 hq
    (symAdd_sum_allParams_unconditional hq0 hqR)
    (diffHyp_unconditional hq0 hqR)
