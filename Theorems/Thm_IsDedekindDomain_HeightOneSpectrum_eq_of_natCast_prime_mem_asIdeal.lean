import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.eq_of_natCast_prime_mem_asIdeal
    {r : ℕ} (hr : r.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((r : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal.solution
