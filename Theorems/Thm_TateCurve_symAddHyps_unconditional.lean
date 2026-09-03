import Mathlib
import Definitions.Def_TateCurve_XMultAlignment
import P2M.Util
import P2M.Sol.S_TateCurve_symAddHyps_unconditional

open scoped NNReal
theorem TateCurve.symAddHyps_unconditional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : TateCurve.SymAddHyps q := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_symAddHyps_unconditional.solution
