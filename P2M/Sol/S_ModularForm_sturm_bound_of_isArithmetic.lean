import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj
import Theorems.Thm_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_nat_mul
import P2M.Util
namespace P2MW.S_ModularForm_sturm_bound_of_isArithmetic

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

theorem solution {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} {f : ModularForm 𝒢 k} (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h : (↑((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 := by
  obtain ⟨M, hM, hconj⟩ := Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj 𝒢
  haveI : Fact (IsCusp OnePoint.infty 𝒢) := ⟨𝒢.isCusp_of_mem_strictPeriods one_pos h1⟩
  refine f.eq_zero_of_lt_order_qExpansion_of_isArithmetic hM hconj ?_
  refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _ _ fun n hn ↦ ?_)
  have := UpperHalfPlane.qExpansion_coeff_nat_mul one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f h1) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) hM n
  rw [mul_one] at this
  rw [this]
  split_ifs with hd
  · apply PowerSeries.coeff_of_lt_order
    refine lt_of_le_of_lt ?_ h
    exact_mod_cast Nat.div_le_of_le_mul (by lia)
  · rfl
end
