import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsArchTestFactor_exists_isArchTestFactor_nonneg_norm_le

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.IsArchTestFactor.exists_isArchTestFactor_nonneg_norm_le
    (F : Type) [Field F] [NumberField F]
    (φa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor F φa) :
    ∃ Ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      AutomorphicForm.IsArchTestFactor F Ψ ∧
      (∀ g : GL (Fin 2) (InfiniteAdeleRing F), 0 ≤ (Ψ g).re ∧ (Ψ g).im = 0) ∧
      ∀ g : GL (Fin 2) (InfiniteAdeleRing F), ‖φa g‖ ≤ (Ψ g).re := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsArchTestFactor_exists_isArchTestFactor_nonneg_norm_le.solution
