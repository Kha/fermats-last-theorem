import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq
    {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]
    (j j' : T) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hint : IsIntegral ↥(Algebra.adjoin A ({j} : Set T)) j') (hint' : IsIntegral ↥(Algebra.adjoin A ({j'} : Set T)) j)
    (h3 : ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf A T j' →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf A T j ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf A T j ∧ s = 1 + j⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf A T j)
    (h4 : ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf A T j →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf A T j' ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf A T j' ∧ s = 1 + j'⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf A T j')
    (σ : T ≃ₐ[A] T) (hσ : σ j' = j') :
    ∃ Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) //
              y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y} →
            {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) //
              y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y},
      Function.Bijective Φ ∧
      (∀ y₁ y₂ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) //
              y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y},
        y₁.1 ≤ y₂.1 ↔ (Φ y₁).1 ≤ (Φ y₂).1) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ y.1 ∧ σ.symm f * (h : T) = (g : T))) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ (Φ y).1 ∧ g ∈ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ y.1 ∧ g ∈ y.1 ∧ σ.symm f * (h : T) = (g : T))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq.solution
