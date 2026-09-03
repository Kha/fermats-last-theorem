import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidHom_exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range

theorem MonoidHom.exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range
    {G : Type*} [Group G] {k Ω : Type} [Field k] [Finite k] [Field Ω]
    (ι : k →+* Ω) (χ₁ χ₂ : G →* Ωˣ)
    (hadd : ∀ g, (χ₁ g : Ω) + χ₂ g ∈ ι.range) (hmul : ∀ g, (χ₁ g : Ω) * χ₂ g ∈ ι.range) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀) (ρ₀ : G →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      (∀ g, χ₁ g = 1 → χ₂ g = 1 → ρ₀ g = 1) ∧
      (∀ g, ι (LinearMap.trace k V₀ (ρ₀ g).toLinearMap) = χ₁ g + χ₂ g) ∧
      (∀ g, ι (LinearMap.det (ρ₀ g).toLinearMap) = χ₁ g * χ₂ g) := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range.solution
