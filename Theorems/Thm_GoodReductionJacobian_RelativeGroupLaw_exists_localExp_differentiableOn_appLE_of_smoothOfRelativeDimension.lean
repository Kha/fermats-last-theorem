import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f) (hc : L.IsCommutative)
    {g : ℕ} (hsm : SmoothOfRelativeDimension g f) :
    ∃ (r : ℝ) (_ : 0 < r) (exp₀ : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
      (U : G.Opens) (_ : IsAffineOpen U) (t : Fin g → Γ(G, U))
      (hU : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ U),

      exp₀ 0 = L.one (𝟙 (Spec (CommRingCat.of ℂ))) ∧

      (∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
        v + w ∈ Metric.ball (0 : Fin g → ℂ) r →
        exp₀ (v + w) = L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (exp₀ v) (exp₀ w)) ∧

      Set.InjOn exp₀ (Metric.ball (0 : Fin g → ℂ) r) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
        ∃ F : (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
          ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V), v ∈ Metric.ball (0 : Fin g → ℂ) r →
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE V ⊤ h) φ)) ∧

      (∃ (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (F : (Fin g → ℂ) → (Fin g → ℂ)),
          (∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r),
            F v = fun i : Fin g =>
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE U ⊤ (hU v hv)) (t i))) ∧
          HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) 0) ∧

      (∃ (fs : Finset (Γ(G, U))) (ε : ℝ) (h1 : ⊤ ≤ (L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1 ⁻¹ᵁ U), 0 < ε ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
            (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                  (((L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1.appLE U ⊤ h1) φ)‖ < ε) →
            ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, exp₀ v = P) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension.solution
