import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero"

theorem CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))
    {u : ↥P → K} (hu : u ∈ holOn K P) (h0 : ∀ z : ↥P, u z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥P, Valued.v δ ≤ Valued.v (u z) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero.solution
