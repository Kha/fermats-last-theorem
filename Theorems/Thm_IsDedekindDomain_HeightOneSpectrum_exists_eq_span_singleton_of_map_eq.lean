import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq

theorem IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (μ : K →+* K) (N : IsDedekindDomain.HeightOneSpectrum R → Option (IsDedekindDomain.HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w) (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ), w.valuation K h ≤ WithZero.exp (-(k : ℤ)) → v.valuation K (μ h) ≤ WithZero.exp (-(k : ℤ))) (g : K) (t₀ : IsDedekindDomain.HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = WithZero.exp (-1)) (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) : ∃ r : R, t₀.asIdeal = Ideal.span {r} := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq.solution
