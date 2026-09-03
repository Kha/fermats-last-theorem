import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_ringHom_comp_eq_of_fstHom_comp_eq

set_option autoImplicit false

theorem CerednikDrinfeld.ringHom_comp_eq_of_fstHom_comp_eq
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (κ : Type) [Field κ] [CharP κ p]
    (ψ : WittVector p k →+* DualNumber κ)
    (s : DualNumber κ →ₐ[κ] DualNumber κ)
    (hs : (TrivSqZeroExt.fstHom κ κ κ).comp s = TrivSqZeroExt.fstHom κ κ κ) :
    (s : DualNumber κ →+* DualNumber κ).comp ψ = ψ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_ringHom_comp_eq_of_fstHom_comp_eq.solution
