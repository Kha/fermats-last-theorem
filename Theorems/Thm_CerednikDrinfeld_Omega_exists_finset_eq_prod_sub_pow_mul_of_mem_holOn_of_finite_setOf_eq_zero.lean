import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~exists_mem_holOn_eq_sub_mul_of_apply_eq_zero~exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset"

theorem CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (hfin : Set.Finite {z : ↥S | f z = 0})

    (hdisc : ∀ z : ↥S, f z = 0 → ∃ r : K, r ≠ 0 ∧ ∀ w : K, Valued.v (w - (z : K)) ≤ Valued.v r → w ∈ S) :
    ∃ (Z : Finset ↥S) (k : ↥S → ℕ) (u : ↥S → K),
      u ∈ holOn K S ∧ (∀ z : ↥S, u z ≠ 0) ∧
      (∀ p : ↥S, p ∈ Z ↔ 1 ≤ k p) ∧
      ∀ z : ↥S, f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero.solution
