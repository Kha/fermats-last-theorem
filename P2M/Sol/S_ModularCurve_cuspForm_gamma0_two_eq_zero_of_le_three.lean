import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.Nat.Squarefree
import Theorems.Thm_ModularForm_sturm_bound_Gamma0
import Theorems.Thm_ModularCurve_Gamma0_index
import P2M.Util
namespace P2MW.S_ModularCurve_cuspForm_gamma0_two_eq_zero_of_le_three
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single
set_option autoImplicit false

namespace ModularCurve p2m_export "ModularCurve" "Gamma0_index dedekindPsi" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.cuspForm_gamma0_two_eq_zero_of_le_three (p : ℕ) (hp : p = 2 ∨ p = 3) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) : f = 0 := by
  have hpr : p.Prime := by
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  haveI : NeZero p := ⟨hpr.ne_zero⟩
  have hψ : ModularCurve.dedekindPsi p = p + 1 := by
    rw [ModularCurve.dedekindPsi, Nat.divisors_filter_squarefree_of_squarefree hpr.prime.squarefree,
      hpr.divisors, Finset.sum_pair hpr.one_lt.ne, Nat.div_one, Nat.div_self hpr.pos]
  have hidx : (CongruenceSubgroup.Gamma0 p).index = p + 1 := (ModularCurve.Gamma0_index p).trans hψ
  have hp3 : p ≤ 3 := by rcases hp with rfl | rfl <;> norm_num
  have hF : (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2) = 0 := by
    refine ModularForm.sturm_bound_Gamma0 p (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2) ?_
    intro n hn
    obtain rfl : n = 0 := by omega
    have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 p :
        Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
      rw [CongruenceSubgroup.strictPeriods_Gamma0]
      exact AddSubgroup.mem_zmultiples 1
    exact CuspFormClass.qExpansion_coeff_zero f one_pos h1
  ext z
  exact DFunLike.congr_fun hF z

theorem solution (p : ℕ) (hp : p = 2 ∨ p = 3) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) : f = 0 :=
  ModularCurve.cuspForm_gamma0_two_eq_zero_of_le_three p hp f
