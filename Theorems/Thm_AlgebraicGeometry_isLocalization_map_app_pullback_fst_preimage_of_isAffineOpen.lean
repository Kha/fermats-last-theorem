import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
    {R : Type u} [CommRing R] (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
    {B : Scheme.{u}} (q : B ⟶ Spec (CommRingCat.of R)) (V : B.Opens) (hV : IsAffineOpen V) :
    letI := ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T)))).app V).hom.toAlgebra
    IsLocalization
      (M.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop ≫
          B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom : R →* Γ(B, V)))
      Γ(pullback q (Spec.map (CommRingCat.ofHom (algebraMap R T))),
        pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⁻¹ᵁ V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen.solution
