import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~exists_mem_holOn_eq_sub_mul_of_apply_eq_zero"

theorem CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0)
    (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (hHc : ∀ h ∈ H, Valued.v (h - c) < Valued.v R)
    (hdisj : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Valued.v (ρ h) < Valued.v (h - h'))
    (E : Finset K)
    (hU : ∀ z : K, Valued.v (z - c) < Valued.v R → (∀ h ∈ H, Valued.v (ρ h) < Valued.v (z - h)) → z ∈ S)
    (hout : ∀ z : K, Valued.v (z - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v (z - e)) → z ∈ S)
    (hin : ∀ h ∈ H, ∀ z : K, Valued.v (z - h) = Valued.v (ρ h) →
      (∀ e ∈ E, Valued.v (ρ h) ≤ Valued.v (z - e)) → z ∈ S)
    (hout₀ : ∃ z : ↥S, Valued.v ((z : K) - c) = Valued.v R ∧
      (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0)
    (hin₀ : ∀ h ∈ H, ∃ z : ↥S, Valued.v ((z : K) - h) = Valued.v (ρ h) ∧
      (∀ e ∈ E, Valued.v (ρ h) ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0) :
    {z : ↥S | Valued.v ((z : K) - c) < Valued.v R ∧
      (∀ h ∈ H, Valued.v (ρ h) < Valued.v ((z : K) - h)) ∧ f z = 0}.Finite := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn.solution
