import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v w

theorem AlgebraicCurve.CurveModel.existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
    {κ : Type u} [Field κ] [IsAlgClosed κ] {k : Type u} [Field k] [IsAlgClosed k] (φ : κ →+* k)
    {F₀ : Type v} [Field F₀] [Algebra κ F₀] {F : Type w} [Field F] [Algebra k F]
    (M₀ : CurveModel κ F₀) (M : CurveModel k F)
    (e : M.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ)))
    (he : e.hom ≫ pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom φ)) = M.toBase)
    (ψ : F₀ →+* F)

    (hsq : ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U))] (s : Γ(M₀.C, U)),
      M.ffEquiv.symm (M.C.germToFunctionField ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom s)) =
        ψ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s))) :

    (∀ y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}, ∃! y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1) ∧

    (∀ (y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}) (y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1 →
      (M.pointEquivPlace y).toValuationSubring.comap ψ = (M₀.pointEquivPlace y₀).toValuationSubring ∧
        ∀ f : F₀, (M.pointEquivPlace y).ord (ψ f) = (M₀.pointEquivPlace y₀).ord f) ∧

    (∀ Q : Place k F,
      (∀ (y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}) (y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
        y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1 → Q ≠ M.pointEquivPlace y) →
      ∀ f : F₀, f ≠ 0 → Q.ord (ψ f) = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq.solution
