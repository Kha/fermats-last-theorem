import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_v_apply_eq_on_circle_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0) (E : Finset K)
    (hS : ∀ z : K, Valued.v (z - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v (z - e)) → z ∈ S)
    (h₀ : ∃ z : ↥S, Valued.v ((z : K) - c) = Valued.v R ∧ (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ Z : Finset K,
      (∀ z : ↥S, Valued.v ((z : K) - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) →
        Valued.v (f z) ≤ Valued.v s) ∧
      (∀ z : ↥S, Valued.v ((z : K) - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) →
        (∀ ζ ∈ Z, Valued.v R ≤ Valued.v ((z : K) - ζ)) → Valued.v (f z) = Valued.v s) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn.solution
