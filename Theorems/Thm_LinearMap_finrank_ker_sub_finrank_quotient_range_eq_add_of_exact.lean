import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact

set_option autoImplicit false

universe u v

theorem LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₁)] [FiniteDimensional k (B₁ ⧸ LinearMap.range d₁)]
    [FiniteDimensional k (LinearMap.ker d₃)] [FiniteDimensional k (B₃ ⧸ LinearMap.range d₃)] :
    FiniteDimensional k (LinearMap.ker d₂) ∧ FiniteDimensional k (B₂ ⧸ LinearMap.range d₂) ∧
    (Module.finrank k (LinearMap.ker d₂) : ℤ) - Module.finrank k (B₂ ⧸ LinearMap.range d₂)
      = ((Module.finrank k (LinearMap.ker d₁) : ℤ) - Module.finrank k (B₁ ⧸ LinearMap.range d₁))
        + ((Module.finrank k (LinearMap.ker d₃) : ℤ) - Module.finrank k (B₃ ⧸ LinearMap.range d₃)) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact.solution
