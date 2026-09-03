import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~v_sub_eq_max_of_mem_affinoid_zero_of_not_mem"

theorem CerednikDrinfeld.Omega.v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K] [IsAlgClosed K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K)
    {f g : ↥(affinoid ϖ₁ 0) → K} (hf : f ∈ holOn K (affinoid ϖ₁ 0)) (hg : g ∈ holOn K (affinoid ϖ₁ 0))
    (hfg : f * g = 1) (z z' : ↥(affinoid ϖ₁ 0)) :
    Valued.v (f z) = Valued.v (f z') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one.solution
