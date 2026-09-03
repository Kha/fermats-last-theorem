import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact

open NumberField FLT.SmoothVectors

theorem AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) {K : Set ↥(finiteAdelicGL2Subgroup F)} (hK : IsCompact K) :
    Set.Finite ((· • (RightTranslationFn.mk φ :
      RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) '' K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact.solution
