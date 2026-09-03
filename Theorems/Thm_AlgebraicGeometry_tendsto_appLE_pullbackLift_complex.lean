import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_tendsto_appLE_pullbackLift_complex
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology

theorem AlgebraicGeometry.tendsto_appLE_pullbackLift_complex
    {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)} {g : Y ⟶ Spec (CommRingCat.of ℂ)}
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
    (hP : ∀ (U : X.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U,
          ∀ s : Γ(X, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hx) s))))
    (P' : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (Q' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g)
    (hP' : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q'.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P' n).1 ⁻¹ᵁ U,
          ∀ s : Γ(Y, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P' n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q'.1.appLE U ⊤ hx) s)))) :
    ∀ (U : (pullback f g).Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ (⟨pullback.lift Q.1 Q'.1 (Q.2.trans Q'.2.symm), by rw [pullback.lift_fst_assoc]; exact Q.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (⟨pullback.lift (P n).1 (P' n).1 ((P n).2.trans (P' n).2.symm), by rw [pullback.lift_fst_assoc]; exact (P n).2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1 ⁻¹ᵁ U,
          ∀ s : Γ((pullback f g), U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((⟨pullback.lift (P n).1 (P' n).1 ((P n).2.trans (P' n).2.symm), by rw [pullback.lift_fst_assoc]; exact (P n).2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((⟨pullback.lift Q.1 Q'.1 (Q.2.trans Q'.2.symm), by rw [pullback.lift_fst_assoc]; exact Q.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1.appLE U ⊤ hx) s))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_tendsto_appLE_pullbackLift_complex.solution
