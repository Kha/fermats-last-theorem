import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.schemeKerStr_baseChange_props
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyOfFiniteType ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    IsSeparated ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    QuasiCompact ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    Flat ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    (∃ π : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶ (O.L.baseChange Λ.σA).schemeKer m,
      IsPullback π ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
        ((O.L.baseChange Λ.σA).schemeKerStr m) (Spec.map (CommRingCat.ofHom (residue ↥A)))) ∧
    (∃ (XK : Scheme.{0}) (qK : XK ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
        (πK : XK ⟶ (O.L.baseChange Λ.σA).schemeKer m),
      IsPullback πK qK ((O.L.baseChange Λ.σA).schemeKerStr m)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) ∧ IsReduced XK) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props.solution
