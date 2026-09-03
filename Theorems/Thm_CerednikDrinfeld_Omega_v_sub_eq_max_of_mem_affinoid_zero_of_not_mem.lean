import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.v_sub_eq_max_of_mem_affinoid_zero_of_not_mem
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K) {z a : K} (hz : z ∈ affinoid ϖ₁ 0) (ha : a ∉ affinoid ϖ₁ 0) :
    Valued.v (z - a) = max 1 (Valued.v a) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem.solution
