import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_exists_isIdempotentElem_apply_eq_zero_isLocalRing_quotient

set_option autoImplicit false

universe u v

theorem IsAdicComplete.exists_isIdempotentElem_apply_eq_zero_isLocalRing_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] (φ : S →ₐ[R] R) :
    ∃ e : S, IsIdempotentElem e ∧ φ e = 0 ∧ IsLocalRing (S ⧸ Ideal.span ({e} : Set S)) := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_exists_isIdempotentElem_apply_eq_zero_isLocalRing_quotient.solution
