import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover

set_option autoImplicit false

open CerednikDrinfeld.Omega hiding inv_mem_holOn_of_forall_le_v_apply linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero mem_holOn_of_forall_mem_holOn_linearPiece_of_cover

theorem CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    (hnt : ∃ y : K, y ≠ 0 ∧ Valued.v y < 1)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    {ι : Type} [Fintype ι] (L M : ι → Finset (K × K))
    (hL : ∀ i, ∀ er ∈ L i, er.2 ≠ 0) (hM : ∀ i, ∀ er ∈ M i, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, ∃ i, (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧ (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2))

    (F : ↥P → K) (E : Finset K)
    (f g : (i : ι) → ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} → K)
    (hf : ∀ i, f i ∈ holOn K {z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)})
    (hg : ∀ i, g i ∈ holOn K {z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)})
    (hgfin : ∀ i, Set.Finite {z : ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} | g i z = 0})
    (hrep : ∀ (i : ι) (z : ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)}),
      (z : K) ∉ E → g i z * F ⟨(z : K), z.2.1⟩ = f i z) :
    ∃ b : Polynomial K, b ≠ 0 ∧ (fun z : ↥P => b.eval (z : K) * F z) ∈ holOn K P := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover.solution
