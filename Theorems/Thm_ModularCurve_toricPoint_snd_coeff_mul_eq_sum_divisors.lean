module

public import Definitions.Def_ModularCurve_TateSlots
public import P2M.Util
public import P2M.Sol.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors

@[expose] public section

open ModularCurve
theorem ModularCurve.toricPoint_snd_coeff_mul_eq_sum_divisors (K : Type*) [Field K] (p : ℕ) (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) : (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.solution
