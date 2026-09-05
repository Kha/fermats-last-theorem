module

public import Mathlib
public import Definitions.Def_ModularCurve_CharPReduction
public import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized

@[expose] public section
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring
attribute [-simp] ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (g : ↥(modularFunctionFieldBar (1 * q))) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red ∨
      ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.solution
