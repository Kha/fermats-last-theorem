import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology

theorem Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : S)
    (hdt : KaehlerDifferential.D ℂ S t ∉ (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S))) :
    ∃ (r : ℝ) (𝒰 : Set (S →ₐ[ℂ] ℂ)), 0 < r ∧ σ₀ ∈ 𝒰 ∧
      Set.BijOn (fun σ : S →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r) ∧
      (∀ s : S, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t)) ∧

      (∀ σ ∈ 𝒰, ∃ (fs : Finset S) (ε : ℝ), 0 < ε ∧
        ∀ σ' : S →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖σ' s - σ s‖ < ε) → σ' ∈ 𝒰) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential.solution
