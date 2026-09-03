import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mulArchimedean_valueGroup_iff_forall_exists_pow_le

set_option autoImplicit false

theorem ValuationSubring.mulArchimedean_valueGroup_iff_forall_exists_pow_le {L : Type*} [Field L] (A : ValuationSubring L) :
    MulArchimedean A.ValueGroup ↔
      (∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
        ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mulArchimedean_valueGroup_iff_forall_exists_pow_le.solution
