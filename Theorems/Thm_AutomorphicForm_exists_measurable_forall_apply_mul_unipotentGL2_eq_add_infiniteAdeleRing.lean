import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField

theorem AutomorphicForm.exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K] :
    ∃ y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) → mixedEmbedding.mixedSpace K,
      Measurable[borel _] y ∧
      ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (x : InfiniteAdeleRing K),
        y ((g * AutomorphicForm.unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
          y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) + InfiniteAdeleRing.ringEquiv_mixedSpace K x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.solution
