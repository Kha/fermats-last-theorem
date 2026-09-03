import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)

    (hval : ∀ a : K₀, a ≠ 0 → ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ k)
    {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    ∃ g : PGL(2, K₀),
      pmoebius K₀ g⁻¹ z ∈ affinoid ϖ 0 ∨
      (Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (pmoebius K₀ g⁻¹ z) ∧ Valued.v (pmoebius K₀ g⁻¹ z) < 1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted.solution
