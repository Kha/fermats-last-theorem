import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (t : AdelicGL2 (𝓞 F) F)
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    letI := adeleBorel (𝓞 F) F
    ∃ C : ℝ, ∀ s ∈ centreCutSiegelSet F c u d₁ d₂,
      Summable (fun ξ : F => adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)) ∧
      adelicHeight F (s * t) ^ (σ + 1 / 2)
          + ∑' ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)
        ≤ C * archHeight F (glArch (𝓞 F) F s) ^ (σ + 1 / 2) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.solution
