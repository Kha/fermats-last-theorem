import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt"

theorem CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    (U Λ : Finset (K × K)) (hU : ∀ er ∈ U, er.2 ≠ 0) (hΛ : ∀ er ∈ Λ, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, (∃ er ∈ U, Valued.v (z - er.1) ≤ Valued.v er.2) ∨ (∃ er ∈ Λ, Valued.v er.2 ≤ Valued.v (z - er.1)))

    (F : ↥P → K)
    (hFU : ∀ er ∈ U, (fun z : ↥{z : K | z ∈ P ∧ Valued.v (z - er.1) ≤ Valued.v er.2} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ Valued.v (z - er.1) ≤ Valued.v er.2})
    (hFΛ : ∀ er ∈ Λ, (fun z : ↥{z : K | z ∈ P ∧ Valued.v er.2 ≤ Valued.v (z - er.1)} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ Valued.v er.2 ≤ Valued.v (z - er.1)}) :
    F ∈ holOn K P := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover.solution
