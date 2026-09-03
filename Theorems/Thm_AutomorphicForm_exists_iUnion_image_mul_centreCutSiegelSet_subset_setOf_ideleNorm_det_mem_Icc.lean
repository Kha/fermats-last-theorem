import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ α β : ℝ, 0 < α ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ⊆
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc.solution
