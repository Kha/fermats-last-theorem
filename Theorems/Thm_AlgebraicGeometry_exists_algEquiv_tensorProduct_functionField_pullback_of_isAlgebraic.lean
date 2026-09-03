import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
theorem AlgebraicGeometry.exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic
    {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K'] [Algebra.IsAlgebraic K K']
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [IsIntegral ↑(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))] :
    letI := (baseToFunctionField x).toAlgebra
    letI := (baseToFunctionField
      (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))).toAlgebra
    ∃ Φ : K' ⊗[K] X.functionField ≃ₐ[K']
        (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField,
      ∀ (U : X.Opens) [hU : Nonempty (U : Scheme.{u})]
        [hU' : Nonempty (((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U : (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).Opens) : Scheme.{u})]
        (s : Γ(X, U)),
        Φ (1 ⊗ₜ X.germToFunctionField U s) =
          (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).germToFunctionField
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic.solution
