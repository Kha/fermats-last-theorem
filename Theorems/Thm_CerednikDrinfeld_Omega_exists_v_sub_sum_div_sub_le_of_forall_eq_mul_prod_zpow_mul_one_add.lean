import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero"

theorem CerednikDrinfeld.Omega.exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (f h : ↥(holRing ϖ)) (c : K) (m : K₀ → ℤ) (δ : Γ₀) (hδ : δ < 1)
    (hf : ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ affinoid ϖ 0 →
      (f : ↥(upperHalfPlane K₀ K) → K) z =
          c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * (1 + (h : ↥(upperHalfPlane K₀ K) → K) z) ∧
      Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) ≤ δ)
    (b : ↥(upperHalfPlane K₀ K)) (hb : (b : K) ∈ affinoid ϖ 0) :
    ∃ d : K, Valued.v d ≤ 1 ∧
      Valued.v (d - ∑ t ∈ T, (m t : K) / ((b : K) - algebraMap K₀ K t)) ≤ δ ∧
      ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((z : K) - (b : K)) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) b * (1 + d * ((z : K) - (b : K))))
          ≤ Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) b) * Valued.v ((z : K) - (b : K)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add.solution
