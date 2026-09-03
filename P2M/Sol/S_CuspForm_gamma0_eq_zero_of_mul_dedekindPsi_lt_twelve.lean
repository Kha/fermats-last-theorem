import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularForm_sturm_bound_Gamma0
import Theorems.Thm_ModularCurve_Gamma0_index
import P2M.Util
namespace P2MW.S_CuspForm_gamma0_eq_zero_of_mul_dedekindPsi_lt_twelve
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N] (k : ℤ)
    (h : k * (ModularCurve.dedekindPsi N : ℤ) < 12) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  have hD : (k * ((CongruenceSubgroup.Gamma0 N).index : ℤ)).toNat / 12 = 0 := by
    rw [ModularCurve.Gamma0_index N]
    apply Nat.div_eq_of_lt
    omega
  have h0 : (ModularFormClass.modularForm f : ModularForm (CongruenceSubgroup.Gamma0 N) k) = 0 := by
    refine ModularForm.sturm_bound_Gamma0 N (ModularFormClass.modularForm f) ?_
    intro n hn
    rw [hD] at hn
    obtain rfl := Nat.le_zero.mp hn
    simp [UpperHalfPlane.qExpansion_coeff, CuspFormClass.cuspFunction_apply_zero f one_pos hΓ]
  ext τ
  have := congrArg (fun g : ModularForm (CongruenceSubgroup.Gamma0 N) k => g τ) h0
  simpa using this
