import Mathlib
import Definitions.Def_TateCurve_TateParameter
import P2M.Util
import P2M.Sol.S_TateCurve_nnnorm_c_six

open scoped NNReal
open scoped NNReal in
theorem TateCurve.nnnorm_c_six {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q : K} (hq : ‖q‖₊ < 1) :
    ‖(TateCurve.curve q).c₆‖₊ = 1 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_nnnorm_c_six.solution
