import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.inv_mem_holOn_of_forall_le_v_apply
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (S : Set K) {g : ↥S → K} (hg : g ∈ holOn K S)
    (δ : K) (hδ : δ ≠ 0) (hb : ∀ z : ↥S, Valued.v δ ≤ Valued.v (g z)) :
    (fun z : ↥S => (g z)⁻¹) ∈ holOn K S := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply.solution
