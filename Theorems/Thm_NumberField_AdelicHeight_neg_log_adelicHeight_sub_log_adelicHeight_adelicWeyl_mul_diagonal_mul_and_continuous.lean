import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous
    (F : Type) [Field F] [NumberField F] :
    (∀ (h : AdelicGL2 (𝓞 F) F),
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 →
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0 →
      ∀ g : AdelicGL2 (𝓞 F) F,
        -Real.log (NumberField.AdelicHeight.adelicHeight F (h * g))
            - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * (h * g))) =
          -Real.log (NumberField.AdelicHeight.adelicHeight F g)
            - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g))) ∧
    Continuous (fun g : AdelicGL2 (𝓞 F) F =>
      -Real.log (NumberField.AdelicHeight.adelicHeight F g)
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous.solution
