import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_ker_smul_top_sup_span_kaehlerDifferentialD_eq_top_of_bijOn_of_differentiableOn

set_option autoImplicit false

open Topology

theorem Algebra.ker_smul_top_sup_span_kaehlerDifferentialD_eq_top_of_bijOn_of_differentiableOn
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t)) :
    ∀ σ ∈ 𝒰, (RingHom.ker σ.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
        Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_ker_smul_top_sup_span_kaehlerDifferentialD_eq_top_of_bijOn_of_differentiableOn.solution
