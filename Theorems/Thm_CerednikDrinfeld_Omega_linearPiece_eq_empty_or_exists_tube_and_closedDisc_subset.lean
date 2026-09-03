import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hnt : ∃ y : K, y ≠ 0 ∧ Valued.v y < 1)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    (L M : Finset (K × K)) (hL : ∀ er ∈ L, er.2 ≠ 0) (hM : ∀ er ∈ M, er.2 ≠ 0)
    (Q : Set K) (hQ : ∀ z : K, z ∈ Q ↔ z ∈ P ∧ (∀ er ∈ L, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
      (∀ er ∈ M, Valued.v (z - er.1) ≤ Valued.v er.2)) :
    ((∀ z : K, z ∉ Q) ∨
      ∃ (c₁ R₁ : K) (H₁ : Finset K) (ρ₁ : K → K), R₁ ≠ 0 ∧ (∀ h ∈ H₁, ρ₁ h ≠ 0) ∧
        ∀ z : K, z ∈ Q ↔ Valued.v (z - c₁) ≤ Valued.v R₁ ∧ ∀ h ∈ H₁, Valued.v (ρ₁ h) ≤ Valued.v (z - h)) ∧
    (∀ z ∈ Q, ∃ r : K, r ≠ 0 ∧ ∀ w : K, Valued.v (w - z) ≤ Valued.v r → w ∈ Q) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset.solution
