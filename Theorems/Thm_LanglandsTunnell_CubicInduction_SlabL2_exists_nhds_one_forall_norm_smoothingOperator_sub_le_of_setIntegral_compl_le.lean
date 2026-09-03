import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : Continuous F) (K C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) (hC : IsCompact C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : AdelicGL 3 (𝓞 ℚ) ℚ), ∃ δ : ℝ, 0 < δ ∧ ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      (∀ g, 0 ≤ (φ g).re ∧ (φ g).im = 0) → tsupport φ ⊆ C →
      Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) →
      ∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) = 1 →
      ∫ g in Uᶜ, (φ g).re ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤ δ →
        ∀ x ∈ K, ‖smoothingOperator φ F x - F x‖ ≤ ε := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le.solution
