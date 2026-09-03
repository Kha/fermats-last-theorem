import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart
attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of Sc)} (L : RelativeGroupLaw Sc f) {g : ℕ} (hsm : SmoothOfRelativeDimension g f)
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰)
    (hdt₁ : ((RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
        Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤)) :
    ∃ (ε ρ' : ℝ) (_ : 0 < ε) (_ : 0 < ρ') (_ : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r)
      (U₁ : G.Opens) (_ : IsAffineOpen U₁) (s₁ : Fin g → Γ(G, U₁)) (v₁ : Fin g → ℂ)
      (ψ₁ : (σ : Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f)
      (hU₁ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ', ⊤ ≤ (ψ₁ σ v).1 ⁻¹ᵁ U₁)
      (h1U₁ : ⊤ ≤ (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 ⁻¹ᵁ U₁),

      ψ₁ σ₁ v₁ = L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom)) ∧

      (∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε) (v : Fin g → ℂ) (hv : v ∈ Metric.ball v₁ ρ')
        (i : Fin g), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ v).1.appLE U₁ ⊤ (hU₁ σ hσ hz v hv)) (s₁ i)) = v i) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ', ∀ (hV : ⊤ ≤ (ψ₁ σ v).1 ⁻¹ᵁ V),
            F (σ t, v) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ v).1.appLE V ⊤ hV) φ)) ∧

      (∃ (fs₁ : Finset (Γ(G, U₁))) (η₁ : ℝ), 0 < η₁ ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
          ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U₁),
            (∀ φ ∈ fs₁, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P).1.appLE U₁ ⊤ hP) φ) - (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1.appLE U₁ ⊤ h1U₁) φ)‖ < η₁) →
            ∃ v ∈ Metric.ball v₁ ρ', ψ₁ σ v = P) ∧

      (∃ o : ℂ → (Fin g → ℂ), DifferentiableOn ℂ o (Metric.ball (σ₁ t) ε) ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
          o (σ t) ∈ Metric.ball v₁ ρ' ∧ ψ₁ σ (o (σ t)) = L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))) ∧

      (∃ (ρ₂ : ℝ) (M : ℂ → (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ)), 0 < ρ₂ ∧ ρ₂ ≤ ρ' ∧
        DifferentiableOn ℂ (fun p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) => M p.1 p.2.1 p.2.2)
          (Metric.ball (σ₁ t) ε ×ˢ (Metric.ball v₁ ρ₂ ×ˢ Metric.ball v₁ ρ₂)) ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ₂, ∀ w ∈ Metric.ball v₁ ρ₂,
          M (σ t) v w ∈ Metric.ball v₁ ρ' ∧
          ψ₁ σ (M (σ t) v w) = L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart.solution
