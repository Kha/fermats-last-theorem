import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinNumerator_dvd_mul_of_witness

theorem ModularCurve.eisensteinNumerator_dvd_mul_of_witness (ℓ : ℕ) [NeZero ℓ] (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c') (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) (z₀ : ℤ) (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀) (m : ℕ) (H : UpperHalfPlane → ℂ) (hH : Continuous H) (hpow : ∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1) = (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ) : (ModularCurve.eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * z₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinNumerator_dvd_mul_of_witness.solution
