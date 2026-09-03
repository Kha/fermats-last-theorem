import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (a π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v (a - ζ) = Valued.v π)
    (hS : ∀ z : K, Valued.v (z - a) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S)
    (h0 : ∀ z : ↥S, Valued.v ((z : K) - a) < Valued.v π → f z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥S, Valued.v ((z : K) - a) < Valued.v π → Valued.v δ ≤ Valued.v (f z) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero.solution
