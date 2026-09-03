import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite

theorem AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite
    {G : Type*} [Group G] {n : ℕ} (K : Fin n → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
    (f : G → ℂ)
    (hf : ∀ i, ∃ s : Finset (G → ℂ), ∀ k ∈ K i,
      (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))) :
    ∃ (N : ℕ) (a : Fin N → Fin n → G → ℂ) (b : Fin N → G → ℂ),
      (∀ m i, a m i ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ x h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun g => f (x * g * h)}) ∧
      (∀ m i, ∃ t : Finset (G → ℂ), ∀ k' ∈ K i,
          (fun g => a m i (g * k')) ∈ Submodule.span ℂ (t : Set (G → ℂ))) ∧
      (∀ m, b m ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun x => f (x * h)}) ∧
      ∀ (x : G) (k : Fin n → G), (∀ i, k i ∈ K i) →
        f (x * (List.ofFn k).prod) = ∑ m, (∏ i, a m i (k i)) * b m x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite.solution
