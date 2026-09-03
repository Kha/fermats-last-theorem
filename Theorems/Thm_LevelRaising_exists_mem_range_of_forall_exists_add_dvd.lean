import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Field.ZMod
import P2M.Util
import P2M.Sol.S_LevelRaising_exists_mem_range_of_forall_exists_add_dvd

set_option autoImplicit false
theorem LevelRaising.exists_mem_range_of_forall_exists_add_dvd
    {C₁ C₀ : Type*} [AddCommGroup C₁] [AddCommGroup C₀] [Module.Finite ℤ C₀]
    (τ₁ : C₁ →ₗ[ℤ] C₁) (τ₀ : C₀ →ₗ[ℤ] C₀) (β : C₁ →ₗ[ℤ] C₀)
    (hβτ : β ∘ₗ τ₁ = τ₀ ∘ₗ β)
    {p : ℕ} [Fact p.Prime] (a : ℤ)
    (hyp : ∀ h : C₀, ∃ s : Polynomial ℤ, ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, ∃ h' : C₀, (Polynomial.aeval τ₀ s) h = β x + (p : ℤ) • h') :
    ∀ h : C₀, ∃ s : Polynomial ℤ, ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, (Polynomial.aeval τ₀ s) h = β x := by p2m_exact_reverting @_root_.P2MW.S_LevelRaising_exists_mem_range_of_forall_exists_add_dvd.solution
