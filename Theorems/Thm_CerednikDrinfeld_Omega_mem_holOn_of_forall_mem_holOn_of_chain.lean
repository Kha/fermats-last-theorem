import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt"

theorem CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_of_chain
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (k : ℕ) (P : Fin (k + 1) → Set K)
    (hsub : ∀ j, P j ⊆ S) (hcov : S ⊆ ⋃ j, P j)
    (t π : Fin (k + 1) → K) (Z : Fin (k + 1) → Finset K)
    (hπ : ∀ j, j ≠ 0 → π j ≠ 0)
    (hout : ∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i, Valued.v (π j) ≤ Valued.v (z - t j))
    (hin : ∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨ Valued.v (z - t j) < Valued.v (π j))
    (hrim : ∀ j, j ≠ 0 → ∀ z : K, Valued.v (z - t j) = Valued.v (π j) →
      (∀ ζ ∈ Z j, Valued.v (π j) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i)
    (h : ↥S → K)
    (hh : ∀ j, (fun z : ↥(P j) => h ⟨(z : K), hsub j z.2⟩) ∈ holOn K (P j)) :
    h ∈ holOn K S := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain.solution
