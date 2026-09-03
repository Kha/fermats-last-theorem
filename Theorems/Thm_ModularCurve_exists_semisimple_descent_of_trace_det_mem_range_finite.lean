import Mathlib
import Definitions.Def_ModularCurve_ResidualRealization
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite

theorem ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite
    {K L : Type} [Field K] [Field L] [Algebra K L] (M p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (V : Type) [AddCommGroup V] [Module Ω V] (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[Ω] V))
    (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2) (hfin : Finite ρ.range)
    (hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range)
    (hcyc : ModularCurve.CyclotomicDeterminant M p ρ) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀)
      (ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      ModularCurve.CyclotomicDeterminant M p ρ₀ ∧
      ρ.ker ≤ ρ₀.ker ∧
      (∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) ∧
      (∀ W : Submodule k V₀, (∀ σ, ∀ v ∈ W, ρ₀ σ v ∈ W) →
        ∃ W' : Submodule k V₀, (∀ σ, ∀ v ∈ W', ρ₀ σ v ∈ W') ∧ IsCompl W W') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.solution
