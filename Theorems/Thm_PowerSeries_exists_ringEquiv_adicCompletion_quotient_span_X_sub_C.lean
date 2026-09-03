import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
set_option autoImplicit false

theorem PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+*
        (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}),
      ∀ o : O, e (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) o) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) (PowerSeries.C o) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C.solution
