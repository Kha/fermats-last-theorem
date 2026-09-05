module

public import Mathlib
public import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar

@[expose] public section
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

open AlgebraicCurve ModularCurve
theorem ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    ∃ x : modularFunctionFieldBar N, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (modularFunctionFieldBar N)))
        (modularFunctionFieldBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar.solution
