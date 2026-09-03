import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le
    (k : ℤ) (hk : 1 ≤ k) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (wt : ℤ → Submodule ℂ M)
      (E L ε : M →ₗ[ℂ] M),
      IsGL2RealKTypeModule wt E L ε ∧ (∀ n : ℤ, FiniteDimensional ℂ (wt n)) ∧
      IsIrreducibleGL2RealKTypeModule wt E L ε ∧ {n : ℤ | wt n ≠ ⊥}.Infinite ∧
      (∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k))) ∧
      (∀ k' : ℤ, (∃ v ∈ wt k', v ≠ 0 ∧ L v = 0) ↔ k' = k) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le.solution
