import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_slotSubst_tateUnivY

open ModularCurve
theorem ModularCurve.coeff_slotSubst_tateUnivY {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivY) = (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0) - (if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0) + (if n = p * M then (e : K) else 0)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_slotSubst_tateUnivY.solution
