import Mathlib
import P2M.Util
import P2M.Sol.S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq

set_option autoImplicit false

universe u

theorem IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    ∃ (n : ℕ) (e : Fin n → B), CompleteOrthogonalIdempotents e ∧
      ∀ i : Fin n, e i ≠ 0 ∧ ∀ x : B, IsIdempotentElem x → x * e i = 0 ∨ x * e i = e i := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq.solution
