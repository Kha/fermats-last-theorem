module

public import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_slotSubst_tateUnivX

@[expose] public section

open ModularCurve
theorem ModularCurve.coeff_slotSubst_tateUnivX {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivX) = (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) * ((if n = p * M + j * e then (c : K) ^ e else 0) + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0) - (if n = p * M then 2 else 0)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX.solution
