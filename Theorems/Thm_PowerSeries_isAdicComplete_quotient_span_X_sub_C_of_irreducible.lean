import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
set_option autoImplicit false

theorem PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (_ : IsDomain (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsDiscreteValuationRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsAdicComplete
        (IsLocalRing.maximalIdeal (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
        (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})),
      Irreducible (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible.solution
