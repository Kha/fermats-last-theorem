import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_differentiableOn_appLE_pullback_pair_of_relChart
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem AlgebraicGeometry.differentiableOn_appLE_pullback_pair_of_relChart
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} (f : G ⟶ Spec (CommRingCat.of Sc)) {g : ℕ}
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰) (ε ρ' : ℝ) (hε : 0 < ε) (hρ' : 0 < ρ')
    (hεr : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r) (v₀ : Fin g → ℂ)
    (ψ : (Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G))
    (hover : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ',
      ψ σ v ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hAN : ∀ (V : G.Opens) (φ : Γ(G, V)),
      IsOpen {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₀ ρ' ∧
        ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} ∧
      ∃ F : ℂ × (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₀ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ (hV : ⊤ ≤ (ψ σ v) ⁻¹ᵁ V),
          F (σ t, v) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ σ v).appLE V ⊤ hV) φ))

    (pair : (Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ pullback f f))
    (hpair₁ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ w ∈ Metric.ball v₀ ρ',
      pair σ v w ≫ pullback.fst f f = ψ σ v)
    (hpair₂ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ w ∈ Metric.ball v₀ ρ',
      pair σ v w ≫ pullback.snd f f = ψ σ w)
    (V' : (pullback f f).Opens) (φ' : Γ(pullback f f, V')) :
    IsOpen {p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2.1 ∈ Metric.ball v₀ ρ' ∧
        p.2.2 ∈ Metric.ball v₀ ρ' ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (pair σ p.2.1 p.2.2) ⁻¹ᵁ V'} ∧
      ∃ F : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) → ℂ,
        DifferentiableOn ℂ F {p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2.1 ∈ Metric.ball v₀ ρ' ∧
          p.2.2 ∈ Metric.ball v₀ ρ' ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (pair σ p.2.1 p.2.2) ⁻¹ᵁ V'} ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ w ∈ Metric.ball v₀ ρ',
          ∀ (hV : ⊤ ≤ (pair σ v w) ⁻¹ᵁ V'),
            F (σ t, (v, w)) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((pair σ v w).appLE V' ⊤ hV) φ') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_differentiableOn_appLE_pullback_pair_of_relChart.solution
