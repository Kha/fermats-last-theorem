import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ne_zero_apply_mul_archRealGLAt_J_eq_mul_lower_of_finiteDimensional_of_forall_mem

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.exists_ne_zero_apply_mul_archRealGLAt_J_eq_mul_lower_of_finiteDimensional_of_forall_mem
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (lam : ℂ) (hlam : lam ≠ 1 / 4)
    (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ S] (hS : S ≠ ⊥)
    (hsm : ∀ x ∈ S, IsArchSmoothAt hw x)
    (htype : ∀ x ∈ S, HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) x)
    (hΩ : ∀ x ∈ S, archCasimirAt hw x = lam • x)
    (hstab : ∀ x ∈ S,
      (fun g => (archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)) (g * archRealGLAt hw UpperHalfPlane.J)) ∈ S) :
    ∃ ψ ∈ S, ψ ≠ 0 ∧ ∃ cJ : ℂ, ∀ g : AdelicGL2 (𝓞 F) F,
      ψ (g * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H ψ - Complex.I • (archDerivAt hw ArchDir.E ψ + archDerivAt hw ArchDir.Fm ψ)) g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ne_zero_apply_mul_archRealGLAt_J_eq_mul_lower_of_finiteDimensional_of_forall_mem.solution
