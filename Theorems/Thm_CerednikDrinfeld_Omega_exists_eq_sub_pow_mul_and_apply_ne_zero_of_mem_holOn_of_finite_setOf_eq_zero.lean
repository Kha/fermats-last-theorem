import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~exists_mem_holOn_eq_sub_mul_of_apply_eq_zero~exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset"

theorem CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (hfin : Set.Finite {z : ↥S | f z = 0})
    (p : ↥S) (r : K) (hr : r ≠ 0) (hD : ∀ w : K, Valued.v (w - (p : K)) ≤ Valued.v r → w ∈ S) :
    ∃ (k : ℕ) (g : ↥S → K), g ∈ holOn K S ∧ g p ≠ 0 ∧
      ∀ z : ↥S, f z = ((z : K) - (p : K)) ^ k * g z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero.solution
