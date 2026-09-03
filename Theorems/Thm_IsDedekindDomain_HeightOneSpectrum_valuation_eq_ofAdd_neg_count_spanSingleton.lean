import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_ofAdd_neg_count_spanSingleton
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
theorem IsDedekindDomain.HeightOneSpectrum.valuation_eq_ofAdd_neg_count_spanSingleton
    {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    v.valuation K x =
      (↑(Multiplicative.ofAdd (-(FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)))) :
        WithZero (Multiplicative ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_ofAdd_neg_count_spanSingleton.solution
