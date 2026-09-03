import Mathlib
import Theorems.Thm_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt
import Theorems.Thm_Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det
import P2M.Util
import P2M.Sol.S_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance

set_option autoImplicit false

theorem Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance
    (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ) (hn0 : ∀ i : Fin r, (i : ℕ) = 0 → n i = 0)
    {ι : Fin r → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module (ZMod p) (V i j)]
    (φ : ∀ i j, (Fin r → ZMod p) →ᵃ[ZMod p] V i j)
    (hφ : ∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, ∃ x, φ i j x ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) + 1 < p) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p),
      IsUnit U ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U i j) ∨ U i j = 0) ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i j, U i j = (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ)) ∧
      (∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // n a = c}) => d i.1 j.1))) ∧
      (∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, φ i j (d i) ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance.solution
