module

public import Mathlib.RingTheory.LaurentSeries
import P2M.Util
import P2M.Sol.S_ModularCurve_single_div_one_sub_sq

@[expose] public section
attribute [-instance] ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent
attribute [-simp] ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

theorem ModularCurve.single_div_one_sub_sq (K : Type*) [Field K] (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 2 =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_single_div_one_sub_sq.solution
