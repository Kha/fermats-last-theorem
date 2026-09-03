import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min

set_option autoImplicit false

p2m_open "ModularCurve~coeff_slotSubst_tateUnivX"

theorem ModularCurve.coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min
    {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (∀ n : ℕ, n < min j (p - j) → PowerSeries.coeff n (slotSubst K p c j tateUnivX) = 0) ∧
    (j < p - j → PowerSeries.coeff j (slotSubst K p c j tateUnivX) = (c : K)) ∧
    (p - j < j → PowerSeries.coeff (p - j) (slotSubst K p c j tateUnivX) = ((c⁻¹ : Kˣ) : K)) ∧
    (Nontrivial K → 2 * j ≠ p → PowerSeries.order (slotSubst K p c j tateUnivX) = (min j (p - j) : ℕ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min.solution
