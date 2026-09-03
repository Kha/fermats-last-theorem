import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn

set_option autoImplicit false

open Topology

theorem Algebra.exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰) :
    ∃ (fs : Finset Sc) (δ : ℝ), 0 < δ ∧
      ∀ τ : Sc →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖τ s - σ₁ s‖ < δ) →
        τ ∈ 𝒰 ∧ ∀ σ ∈ 𝒰, σ t = τ t → σ = τ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn.solution
