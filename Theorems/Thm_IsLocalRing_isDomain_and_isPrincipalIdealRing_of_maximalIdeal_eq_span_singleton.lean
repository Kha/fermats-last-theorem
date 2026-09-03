import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton

theorem IsLocalRing.isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (τ : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span {τ}) (hτ : ∀ n : ℕ, τ ^ n ≠ 0) :
    IsDomain R ∧ IsPrincipalIdealRing R := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton.solution
