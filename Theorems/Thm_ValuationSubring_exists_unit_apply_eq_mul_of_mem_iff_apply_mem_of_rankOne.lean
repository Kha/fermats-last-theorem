import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne

set_option autoImplicit false

theorem ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
    {L : Type*} [Field L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (σ : L ≃+* L) (hA : ∀ a : L, a ∈ A ↔ σ a ∈ A) (hσπ : σ (π : L) = (π : L)) :
    ∀ a : L, a ≠ 0 → ∃ u : Aˣ, σ a = u * a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne.solution
