import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import P2M.Util
import P2M.Sol.S_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
            (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) * AutomorphicForm.archIdentGL K L y)) =
      ∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
        Real.log
          (AutomorphicForm.WindowedSiegel.topNormSq
              ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L y) : GL (Fin 2) w.Completion) :
                Matrix (Fin 2) (Fin 2) w.Completion) *
            AutomorphicForm.WindowedSiegel.rowNormSq
              ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L y) : GL (Fin 2) w.Completion) :
                Matrix (Fin 2) (Fin 2) w.Completion) /
            ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L y) : GL (Fin 2) w.Completion) :
                Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log.solution
