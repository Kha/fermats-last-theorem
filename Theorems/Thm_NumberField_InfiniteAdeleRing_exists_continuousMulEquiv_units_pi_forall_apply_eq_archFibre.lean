import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ E : (InfiniteAdeleRing L)ˣ ≃ₜ* (∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ),
      ∀ (y : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K),
        E y v = AutomorphicForm.TransversalMeasure.archFibre K L v y := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre.solution
