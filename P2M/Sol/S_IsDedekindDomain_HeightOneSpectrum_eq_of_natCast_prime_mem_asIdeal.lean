import Mathlib
import P2M.Util
namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem natCast_mem_asIdeal_iff' (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_eq_of_prime_mem' {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : Rat.HeightOneSpectrum.natGenerator v = p :=
  (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).1
    ((natCast_mem_asIdeal_iff' v p).1 hv)

theorem solution
    {r : ℕ} (hr : r.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((r : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  have e1 := natGenerator_eq_of_prime_mem' hr w hw
  have e2 := natGenerator_eq_of_prime_mem' hr v hv
  have : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w = Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v :=
    Subtype.ext (e1.trans e2.symm)
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective this
