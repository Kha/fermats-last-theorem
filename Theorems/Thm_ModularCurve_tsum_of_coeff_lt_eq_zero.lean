module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_tsum_of_coeff_lt_eq_zero

@[expose] public section
attribute [-instance] ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent
attribute [-simp] ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

theorem ModularCurve.tsum_of_coeff_lt_eq_zero {K : Type*} [Field K] {δ : ℕ} (hδ : 0 < δ) (f : ℕ → LaurentSeries K) (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0) (g : LaurentSeries K) (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) : ∑' N, f N = g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tsum_of_coeff_lt_eq_zero.solution
