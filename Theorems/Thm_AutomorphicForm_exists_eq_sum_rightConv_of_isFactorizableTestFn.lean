import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.exists_eq_sum_rightConv_of_isFactorizableTestFn (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) :
    ∃ n : ℕ, ∃ g h : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      (∀ k, IsFactorizableTestFn K (g k)) ∧ (∀ k, IsFactorizableTestFn K (h k)) ∧
        ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn.solution
