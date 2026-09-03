import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_isSeparable_jqNModC_of_good
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open ModularCurve
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem ModularCurve.isSeparable_jqNModC_of_good
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (hℓN : ¬ ℓ ∣ N) :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_jqNModC_of_good.solution
