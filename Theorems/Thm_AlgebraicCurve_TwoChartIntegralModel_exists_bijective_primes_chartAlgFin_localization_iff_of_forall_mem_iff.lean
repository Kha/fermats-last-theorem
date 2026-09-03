import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff
    {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T] (j : T)
    (σ : T ≃ₐ[A] T)
    (hσ : ∀ b : T, b ∈ TwoChartIntegralModel.chartAlgFin A T j ↔ σ b ∈ TwoChartIntegralModel.chartAlgFin A T j) :
    ∃ Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} →
            {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
      Function.Bijective Φ ∧
      (∀ y₁ y₂ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
        y₁.1 ≤ y₂.1 ↔ (Φ y₁).1 ≤ (Φ y₂).1) ∧
      (∀ (y : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime})
        (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)),
        b ∈ (Φ y).1 ↔ (⟨σ.symm b, (hσ (σ.symm b)).2 (by rw [AlgEquiv.apply_symm_apply]; exact b.2)⟩ :
          ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ σ.symm f * (h : T) = (g : T))) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ g ∈ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ g ∈ y.1 ∧ σ.symm f * (h : T) = (g : T))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff.solution
