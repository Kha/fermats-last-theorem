import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_functionField_pullback_generates_and_linearIndependent
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.functionField_pullback_generates_and_linearIndependent
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of k)) [IsIntegral Y]
    [IsIntegral (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (prStar : ↑Y.functionField →+* ↑(Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).functionField)
    (hpr : ∀ (U : Y.Opens) (hU : genericPoint Y ∈ U)
      (hU' : genericPoint (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ∈
        (Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹ᵁ U)
      (sec : Y.presheaf.obj (Opposite.op U)),
      prStar ((Y.presheaf.germ U (genericPoint Y) hU).hom sec) =
        ((Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.germ _ (genericPoint (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) hU').hom
          (((Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).app U).hom sec)) :
    (Subfield.closure
        (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∪
          Set.range prStar) = ⊤) ∧
    (∀ (t : Finset ↑Y.functionField),
      (∀ c : t → k, (∑ x : t, AlgebraicCurve.baseToFunctionField g (c x) * (x : ↑Y.functionField)) = 0 → ∀ x : t, c x = 0) →
      ∀ c : t → K, (∑ x : t, AlgebraicCurve.baseToFunctionField (Limits.pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (c x) *
          prStar (x : ↑Y.functionField)) = 0 → ∀ x : t, c x = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_functionField_pullback_generates_and_linearIndependent.solution
