import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_exp_neg_count

open scoped nonZeroDivisors
theorem IsDedekindDomain.HeightOneSpectrum.valuation_eq_exp_neg_count {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) {x : K} (hx : x ≠ 0) : v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_exp_neg_count.solution
