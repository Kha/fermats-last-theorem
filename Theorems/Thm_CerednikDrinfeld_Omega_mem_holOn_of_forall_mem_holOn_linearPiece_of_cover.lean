import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_linearPiece_of_cover
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    {ι : Type} [Fintype ι] (L M : ι → Finset (K × K))
    (hL : ∀ i, ∀ er ∈ L i, er.2 ≠ 0) (hM : ∀ i, ∀ er ∈ M i, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, ∃ i, (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧ (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2))

    (F : ↥P → K)
    (hF : ∀ i, (fun z : ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)}) :
    F ∈ holOn K P := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover.solution
