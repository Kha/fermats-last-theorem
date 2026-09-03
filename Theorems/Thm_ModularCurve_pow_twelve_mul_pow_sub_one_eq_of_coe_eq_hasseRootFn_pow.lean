import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow
attribute [-instance] ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero
attribute [-simp] ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve Polynomial open ModularCurve hiding thetaL_jq_pow_six

theorem ModularCurve.pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (m e₄ e₆ : ℕ) (S : Polynomial κ)
    (hS : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL κ (jqModC κ) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC κ) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC κ ^ (4 * m + e₄ + 2 * e₆) * (jqModC κ - 1728) ^ (3 * m + e₄ + e₆)))
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ)
    (b : ↥(ModularCurve.x1FunctionFieldC κ M)) (hb : (b : LaurentSeries κ) = w.hasseRootFn ^ (p - 1))
    (T : ↥(ModularCurve.x1FunctionFieldC κ M))
    (hT : (T : LaurentSeries κ) =
      intSeriesC κ (w.series ^ 12) / intSeriesC κ (PowerSeries.X * ModularCurve.dedekindEtaUnit)) :
    b ^ 12 * T ^ (p - 1) =
      J ^ (4 * e₄) * (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) ^ (6 * e₆) * (Polynomial.aeval J S) ^ 12 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow.solution
