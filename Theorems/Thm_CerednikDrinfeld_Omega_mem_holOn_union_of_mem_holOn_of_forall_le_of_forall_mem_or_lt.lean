import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S₁ S₂ : Set K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) (Z : Finset K)
    (h₁ : ∀ z ∈ S₁, Valued.v π₀ ≤ Valued.v (z - t₀))
    (h₂ : ∀ z ∈ S₂, z ∈ S₁ ∨ Valued.v (z - t₀) < Valued.v π₀)
    (hC : ∀ z : K, Valued.v (z - t₀) = Valued.v π₀ → (∀ ζ ∈ Z, Valued.v π₀ ≤ Valued.v (z - ζ)) → z ∈ S₁ ∩ S₂)
    (h : ↥(S₁ ∪ S₂) → K)
    (hh₁ : (fun z : ↥S₁ => h ⟨(z : K), Or.inl z.2⟩) ∈ holOn K S₁)
    (hh₂ : (fun z : ↥S₂ => h ⟨(z : K), Or.inr z.2⟩) ∈ holOn K S₂) :
    h ∈ holOn K (S₁ ∪ S₂) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt.solution
