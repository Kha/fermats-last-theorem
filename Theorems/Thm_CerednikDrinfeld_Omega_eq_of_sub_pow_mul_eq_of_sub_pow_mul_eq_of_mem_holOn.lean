import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} (p : ↥S) (r : K) (hr : r ≠ 0) (hD : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ S)
    (π : K) (hπ0 : π ≠ 0) (hπ : Valued.v π < 1)
    (F : ↥S → K) {φ φ' : ↥S → K} (hφ : φ ∈ holOn K S) (hφ' : φ' ∈ holOn K S)
    {e e' : ℕ} (he : e = 0 ∨ φ p ≠ 0) (he' : e' = 0 ∨ φ' p ≠ 0)
    (Z : Set ↥S) (hZ : Z.Finite)
    (h : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e * F z = φ z)
    (h' : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e' * F z = φ' z) :
    e = e' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn.solution
