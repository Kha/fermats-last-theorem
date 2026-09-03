import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild

universe u v
theorem ValuationSubring.apply_eq_self_of_pow_apply_eq_self_of_wild {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hA : ((q : ℕ) : L) ∈ A.nonunits) {σ : L ≃ₐ[K] L}
    (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) {m : ℕ} (hm : m.Coprime q) {y : L}
    (h : (σ ^ m) y = y) : σ y = y := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.solution
