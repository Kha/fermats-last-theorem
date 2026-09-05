module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul

@[expose] public section

theorem IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht0 : t ≠ 0) (ht : (Ideal.span {t}).IsPrime)
    (f : K) (hv : ∃ r s : R, s ∉ Ideal.span {t} ∧ f * algebraMap R K s = algebraMap R K r)
    (hint : ∃ n : ℕ, IsIntegral R (algebraMap R K t ^ n * f)) :
    ∃ r : R, algebraMap R K r = f := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul.solution
