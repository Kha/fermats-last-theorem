import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible

theorem PowerSeries.quotient_span_X_sub_C_pow_of_irreducible
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}).IsPrime ∧
    IsPrincipalIdealRing (PowerSeries W ⧸ Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) ∧
    IsLocalRing (PowerSeries W ⧸ Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) ∧
    Irreducible (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)})
      (PowerSeries.C ϖ)) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible.solution
