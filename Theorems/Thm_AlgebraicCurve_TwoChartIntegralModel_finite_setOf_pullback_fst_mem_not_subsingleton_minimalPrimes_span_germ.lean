import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~finite_setOf_pullback_fst_eq_of_isClosed_singleton"

theorem AlgebraicCurve.TwoChartIntegralModel.finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (Ω : Type u) [Field Ω] [Algebra R Ω] (hΩ : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R Ω a = 0) :
    {z : ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) |
      ¬ ((Ideal.span {(((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤
          ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).base z) trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))} :
        Ideal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk
          ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).base z))).minimalPrimes).Subsingleton}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ.solution
