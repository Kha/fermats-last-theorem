import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_mem_holOn_eq_sub_mul_of_apply_eq_zero

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S) (z₀ : ↥S) (hz₀ : f z₀ = 0)
    (r : K) (hr : r ≠ 0) (hD : ∀ z : K, Valued.v (z - (z₀ : K)) ≤ Valued.v r → z ∈ S) :
    ∃ g : ↥S → K, g ∈ holOn K S ∧ ∀ z : ↥S, f z = ((z : K) - (z₀ : K)) * g z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_eq_sub_mul_of_apply_eq_zero.solution
