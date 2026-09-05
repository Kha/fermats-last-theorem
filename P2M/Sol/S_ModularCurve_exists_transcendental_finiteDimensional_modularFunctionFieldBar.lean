module

public import Mathlib
public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_ModularCurve_transcendental_coeffEmb_jq
import P2M.Sol.S_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import P2M.Util

namespace P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N] :
    ∃ x : modularFunctionFieldBar N, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (modularFunctionFieldBar N)))
        (modularFunctionFieldBar N) :=
  ⟨_, ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N,
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero N⟩
end S_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
end P2MW

public section
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

open AlgebraicCurve ModularCurve
theorem ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    ∃ x : modularFunctionFieldBar N, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (modularFunctionFieldBar N)))
        (modularFunctionFieldBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar.solution
end
