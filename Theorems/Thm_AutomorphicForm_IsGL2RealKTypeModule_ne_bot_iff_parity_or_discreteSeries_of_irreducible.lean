import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsGL2RealKTypeModule_ne_bot_iff_parity_or_discreteSeries_of_irreducible

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.IsGL2RealKTypeModule.ne_bot_iff_parity_or_discreteSeries_of_irreducible
    (M : Type*) [AddCommGroup M] [Module ℂ M]
    (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (hM : IsGL2RealKTypeModule wt E L ε)
    (hadm : ∀ n : ℤ, FiniteDimensional ℂ (wt n))
    (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hinf : {n : ℤ | wt n ≠ ⊥}.Infinite) :
    ((∃ e : ℤ, ∀ n : ℤ, wt n ≠ ⊥ ↔ Even (n - e)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) ∧
    (∀ k : ℤ, 2 ≤ k →
      ((∃ v ∈ wt k, v ≠ 0 ∧ L v = 0) ↔ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsGL2RealKTypeModule_ne_bot_iff_parity_or_discreteSeries_of_irreducible.solution
