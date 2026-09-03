import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub (e : ℤ) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (wt : ℤ → Submodule ℂ M)
      (E L ε : M →ₗ[ℂ] M),
      IsGL2RealKTypeModule wt E L ε ∧ (∀ n : ℤ, FiniteDimensional ℂ (wt n)) ∧
      IsIrreducibleGL2RealKTypeModule wt E L ε ∧ {n : ℤ | wt n ≠ ⊥}.Infinite ∧
      (∀ n : ℤ, wt n ≠ ⊥ ↔ Even (n - e)) ∧
      (∀ (k : ℤ) (v : M), v ∈ wt k → L v = 0 → v = 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub.solution
