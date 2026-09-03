import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem

set_option autoImplicit false

theorem Subgroup.existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem
    {G : Type*} [CommGroup G] (μ F A H : Subgroup G) (hμ : (μ : Set G).Finite)
    (hμF : ∀ ζ ∈ μ, ζ ∈ F → ζ = 1) (hμA : μ ≤ A)
    (hA : ∀ u ∈ A, ∃ ζ ∈ μ, ∃ φ ∈ F, u = ζ * φ)
    (hHF : H ≤ F) (hHA : H ≤ A)
    {m : ℕ} (c : Fin m → G) (hcF : ∀ j, c j ∈ F) (hcA : ∀ j, c j ∈ A)
    (hclass : ∀ φ ∈ F, φ ∈ A → ∃! j : Fin m, φ * (c j)⁻¹ ∈ H) :
    (∀ u ∈ A, ∃! p : μ × Fin m × H, u = (p.1 : G) * c p.2.1 * (p.2.2 : G)) ∧
    ∀ {M : Type*} [AddCommMonoid M] (g : G → M), ((A : Set G) ∩ Function.support g).Finite →
      ∑ᶠ u ∈ (A : Set G), g u = ∑ ζ ∈ hμ.toFinset, ∑ j : Fin m, ∑ᶠ h ∈ (H : Set G), g (ζ * c j * h) := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem.solution
