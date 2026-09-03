import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers

set_option autoImplicit false
universe u v
open IsDedekindDomain
theorem IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers
    {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers.solution
