import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt Rat.isReal_infinitePlace φ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ (Module.finrank ℚ ℚ + 1) (fun z : mixedEmbedding.mixedSpace ℚ =>
      φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z, 0) * g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat.solution
