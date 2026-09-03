import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_not_formallySmooth_of_ringEquiv_adicCompletion_crossingModel

set_option autoImplicit false

open IsLocalRing

theorem RingHom.not_formallySmooth_of_ringEquiv_adicCompletion_crossingModel
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (j : A₀ →+* R)
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal R) R ≃+*
      (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
          MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}))
    (he : ∀ a : A₀,
      e (algebraMap R (AdicCompletion (maximalIdeal R) R) (j a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))) :
    ¬ j.FormallySmooth := by p2m_exact_reverting @_root_.P2MW.S_RingHom_not_formallySmooth_of_ringEquiv_adicCompletion_crossingModel.solution
