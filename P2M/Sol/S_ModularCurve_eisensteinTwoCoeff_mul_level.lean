import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Mathlib.Data.Nat.Prime.Basic
import P2M.Util
namespace P2MW.S_ModularCurve_eisensteinTwoCoeff_mul_level
set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_ModularCurve_eisensteinTwoCoeff_mul_level.ModularCurve"

namespace S09WD4U

private theorem filter_divisors_mul_prime {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    (n * p).divisors.filter (fun d => ¬ p ∣ d) = n.divisors.filter (fun d => ¬ p ∣ d) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hpd⟩
    exact ⟨⟨((hp.coprime_iff_not_dvd.mpr hpd).symm).dvd_of_dvd_mul_right hd, hn⟩, hpd⟩
  · rintro ⟨⟨hd, -⟩, hpd⟩
    exact ⟨⟨dvd_mul_of_dvd_left hd p, mul_ne_zero hn hp.ne_zero⟩, hpd⟩

private theorem sigmaPrimeTo_mul_self {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    sigmaPrimeTo p (n * p) = sigmaPrimeTo p n := by
  simp only [sigmaPrimeTo]
  rw [filter_divisors_mul_prime hp hn]

end S09WD4U

namespace ModularCurve p2m_export "ModularCurve" "sigmaPrimeTo eisensteinTwoCoeff eisensteinTwoCoeff_of_ne_zero" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.eisensteinTwoCoeff_mul_level (p : ℕ) [Fact p.Prime] (n : ℕ) : eisensteinTwoCoeff p (n * p) = eisensteinTwoCoeff p n := by
  have hp : p.Prime := Fact.out
  rcases eq_or_ne n 0 with rfl | hn
  · rw [zero_mul]
  · rw [eisensteinTwoCoeff_of_ne_zero p (mul_ne_zero hn hp.ne_zero),
      eisensteinTwoCoeff_of_ne_zero p hn, S09WD4U.sigmaPrimeTo_mul_self hp hn]

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) : eisensteinTwoCoeff p (n * p) = eisensteinTwoCoeff p n :=
  ModularCurve.eisensteinTwoCoeff_mul_level p n
