import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~finite_setOf_apply_eq_zero_of_v_sub_lt_of_mem_holOn"

theorem CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v π ≤ Valued.v (c - ζ))
    (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) :
    (∀ z : ↥S, Valued.v ((z : K) - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v ((z : K) - ζ)) → f z = 0) ∨
      Set.Finite {z : ↥S | Valued.v ((z : K) - c) ≤ Valued.v π ∧
        (∀ ζ ∈ Z, Valued.v π ≤ Valued.v ((z : K) - ζ)) ∧ f z = 0} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn.solution
