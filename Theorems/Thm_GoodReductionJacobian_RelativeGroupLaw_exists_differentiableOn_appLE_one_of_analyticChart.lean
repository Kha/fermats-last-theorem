import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_differentiableOn_appLE_one_of_analyticChart

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.exists_differentiableOn_appLE_one_of_analyticChart
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of Sc)} (L : RelativeGroupLaw Sc f)
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰)
    (V : G.Opens) (h1V : ⊤ ≤ (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 ⁻¹ᵁ V) (φ : Γ(G, V)) :
    ∃ (ε : ℝ) (F : ℂ → ℂ), 0 < ε ∧ Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r ∧
      DifferentiableOn ℂ F (Metric.ball (σ₁ t) ε) ∧
      ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
        ∃ h : ⊤ ≤ (L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 ⁻¹ᵁ V,
          F (σ t) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (((L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1.appLE V ⊤ h) φ) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_differentiableOn_appLE_one_of_analyticChart.solution
