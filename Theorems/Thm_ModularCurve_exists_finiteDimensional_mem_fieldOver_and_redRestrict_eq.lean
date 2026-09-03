import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

theorem ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] (red : A →+* k) (a : k) (ha : a ∈ Set.range red)
    (f : ↥(modularFunctionFieldBar (1 * q))) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      ((f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * q) K) ∧
        (∃ x : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K x = a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq.solution
