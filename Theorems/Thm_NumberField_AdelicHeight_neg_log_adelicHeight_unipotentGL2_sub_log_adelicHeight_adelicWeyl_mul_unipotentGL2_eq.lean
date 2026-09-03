import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.AdelicHeight.neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq
    (F : Type) [Field F] [NumberField F] (x : AdeleRing (𝓞 F) F) :
    -Real.log (NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x))
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * unipotentGL2 x)) =
      (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (max 1 ‖x.2 v‖) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq.solution
