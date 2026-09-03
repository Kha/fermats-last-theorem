import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_flat_of_smoothOfRelativeDimension_pullback_snd
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation c]
    (U : X.Opens) [Flat (U.ι ≫ c)] {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (h : SmoothOfRelativeDimension 1 (pullback.snd (U.ι ≫ c) x))
    (y : X) (hy : y ∈ U) (hyx : (⟨y, hy⟩ : (U : Scheme.{u})) ∈ Set.range (pullback.fst (U.ι ≫ c) x).base) :
    y ∈ c.smoothLocus := by
  obtain ⟨W, hyW, hW⟩ :=
    AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
      (U.ι ≫ c) x h ⟨y, hy⟩ hyx
  haveI := hW
  haveI : Smooth (W.ι ≫ U.ι ≫ c) := SmoothOfRelativeDimension.smooth 1 _
  have htop : (W.ι ≫ U.ι ≫ c).smoothLocus = ⊤ := Scheme.Hom.smoothLocus_eq_top _
  have h1 : (⟨y, hy⟩ : (U : Scheme.{u})) ∈ (U.ι ≫ c).smoothLocus := by
    have h2 : (⟨⟨y, hy⟩, hyW⟩ : (W : Scheme.{u})) ∈ W.ι ⁻¹ᵁ (U.ι ≫ c).smoothLocus := by
      rw [Scheme.Hom.preimage_smoothLocus_eq, htop]
      trivial
    exact h2
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at h1
  exact h1
