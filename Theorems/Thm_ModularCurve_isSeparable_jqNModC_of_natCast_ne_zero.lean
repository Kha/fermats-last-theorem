import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero (K : Type*) [Field K] (M : ℕ) [NeZero M]
    (hM : (M : K) ≠ 0) :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.solution
