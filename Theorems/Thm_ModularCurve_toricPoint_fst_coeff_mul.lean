module

public import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_toricPoint_fst_coeff_mul

@[expose] public section

open ModularCurve
theorem ModularCurve.toricPoint_fst_coeff_mul (K : Type*) [Field K] (p : ℕ) (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) : (toricPoint K p c).1.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_toricPoint_fst_coeff_mul.solution
