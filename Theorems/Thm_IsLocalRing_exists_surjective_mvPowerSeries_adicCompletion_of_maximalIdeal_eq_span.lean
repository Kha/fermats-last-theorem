import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span
set_option autoImplicit false

theorem IsLocalRing.exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span
    {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
    (ϖ : O) (hϖ : Irreducible ϖ) (g h : R)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap O R ϖ, g, h})
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R))) :
    ∃ (θW : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) →+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (θ : MvPowerSeries (Fin 2) (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) →+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R),
      (∀ o : O, θW (Ideal.Quotient.mk _ (PowerSeries.C o)) = algebraMap R _ (algebraMap O R o)) ∧
      θW (Ideal.Quotient.mk _ PowerSeries.X) = algebraMap R _ (algebraMap O R ϖ) ∧
      Function.Surjective θ ∧
      θ.comp MvPowerSeries.C = θW ∧
      θ (MvPowerSeries.X 0) = algebraMap R _ g ∧
      θ (MvPowerSeries.X 1) = algebraMap R _ h := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span.solution
