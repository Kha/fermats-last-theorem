import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
    (F : Type) [Field F] [NumberField F]
    (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (hκ : κ ≠ 1) :
    ∃ (n : ℕ) (ρ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* Matrix (Fin n) (Fin n) ℂ),
      Continuous ρ ∧ ρ κ ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one.solution
