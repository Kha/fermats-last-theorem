import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top

set_option autoImplicit false
theorem MvPowerSeries.exists_eq_sum_subst_mul_of_span_quotient_eq_top
    {B : Type} [CommRing B] {n d : ℕ} (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (b : Fin d → MvPowerSeries (Fin n) B)
    (hgen : Submodule.span B (Set.range (fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j))) = ⊤)
    (f : MvPowerSeries (Fin n) B) :
    ∃ c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top.solution
