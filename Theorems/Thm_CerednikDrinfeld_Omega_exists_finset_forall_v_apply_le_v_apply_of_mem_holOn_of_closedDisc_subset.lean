import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (c r : K) (hr : r ≠ 0) (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v r → z ∈ S)
    {g : ↥S → K} (hg : g ∈ holOn K S) :
    ∃ E : Finset K, ∀ (z₀ : K) (hz₀ : Valued.v (z₀ - c) = Valued.v r),
      (∀ e ∈ E, Valued.v r ≤ Valued.v (z₀ - e)) →
        ∀ (z : K) (hz : Valued.v (z - c) ≤ Valued.v r),
          Valued.v (g ⟨z, hS z hz⟩) ≤ Valued.v (g ⟨z₀, hS z₀ hz₀.le⟩) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset.solution
