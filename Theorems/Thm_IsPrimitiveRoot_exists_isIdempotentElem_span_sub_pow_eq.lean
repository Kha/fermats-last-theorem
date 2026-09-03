import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_isIdempotentElem_span_sub_pow_eq

set_option autoImplicit false
universe u

theorem IsPrimitiveRoot.exists_isIdempotentElem_span_sub_pow_eq
    {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : 1 < ℓ) (ω : R) (hω : IsPrimitiveRoot ω ℓ)
    (hunit : IsUnit ((ℓ : ℕ) : R)) (hdiff : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
    (b : R) (hb : b ^ ℓ = 1) (k : ℕ) :
    ∃ e : R, IsIdempotentElem e ∧ Ideal.span {b - ω ^ k} = Ideal.span {e} := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_isIdempotentElem_span_sub_pow_eq.solution
