import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve HahnSeries
open scoped MatrixGroups

theorem ModularCurve.qExpand_jqModC_mem_intFormRatiosC_gammaH
    (K : Type*) [Field K] (N N' : ℕ) [NeZero N] [NeZero N'] (hN' : N' ∣ N) (H : Subgroup (ZMod N)ˣ) :
    qExpand K N' (jqModC K) ∈ intFormRatiosC K (CohCarrier.GammaH N H) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH.solution
