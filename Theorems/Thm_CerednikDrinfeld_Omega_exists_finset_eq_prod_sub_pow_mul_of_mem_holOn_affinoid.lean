import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid

set_option autoImplicit false

open CerednikDrinfeld.Omega hiding eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero finite_setOf_apply_eq_zero_of_mem_holOn_affinoid exists_mem_holOn_eq_sub_mul_of_apply_eq_zero

theorem CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {f : ↥(affinoid ϖ n) → K} (hf : f ∈ holOn K (affinoid ϖ n)) (hne : ∃ z : ↥(affinoid ϖ n), f z ≠ 0) :
    ∃ (Z : Finset ↥(affinoid ϖ n)) (k : ↥(affinoid ϖ n) → ℕ) (u : ↥(affinoid ϖ n) → K),
      u ∈ holOn K (affinoid ϖ n) ∧ (∀ z : ↥(affinoid ϖ n), u z ≠ 0) ∧
      (∀ p : ↥(affinoid ϖ n), p ∈ Z ↔ 1 ≤ k p) ∧
      ∀ z : ↥(affinoid ϖ n), f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid.solution
