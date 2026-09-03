import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast

set_option autoImplicit false

open ModularCurve ModularCurve.IgusaScheme AlgebraicCurve

theorem ModularCurve.IgusaScheme.chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (S : Set ↥(modularFunctionFieldFull N)) :
    IgusaScheme.chartAlg N ℓ S =
        TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) S ∧
    (∀ x : ↥(modularFunctionFieldFull N), x ∈ IgusaScheme.chartAlg N ℓ S ↔
        ∃ (a : ↥(modularFunctionFieldFull N)) (s : ℤ), a ∈ TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S ∧
          ¬ ((ℓ : ℤ) ∣ s) ∧ (s : ↥(modularFunctionFieldFull N)) * x = a) ∧
    (∃ (hle : ∀ a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S), (a : ↥(modularFunctionFieldFull N)) ∈ IgusaScheme.chartAlg N ℓ S)
       (e : (↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S) ⧸
              Ideal.span {((ℓ : ℕ) : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S))}) ≃+*
            (↥(IgusaScheme.chartAlg N ℓ S) ⧸ Ideal.span {((ℓ : ℕ) : ↥(IgusaScheme.chartAlg N ℓ S))})),
       ∀ a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S),
         e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ⟨(a : ↥(modularFunctionFieldFull N)), hle a⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast.solution
