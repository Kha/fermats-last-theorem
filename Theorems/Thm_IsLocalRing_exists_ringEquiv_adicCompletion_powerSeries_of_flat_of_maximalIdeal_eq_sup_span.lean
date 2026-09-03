import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span
    (W : Type*) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra W R]
    [IsLocalHom (algebraMap W R)] [Module.Flat W R]
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap W R)))
    (t : R) (ht : maximalIdeal R = (maximalIdeal W).map (algebraMap W R) ⊔ Ideal.span {t})
    (hdim : ringKrullDim (R ⧸ (maximalIdeal W).map (algebraMap W R)) = 1) :
    ∃ e : AdicCompletion (maximalIdeal R) R ≃+* PowerSeries W,
      (∀ a : W, e (algebraMap R (AdicCompletion (maximalIdeal R) R) (algebraMap W R a)) = PowerSeries.C a) ∧
        e (algebraMap R (AdicCompletion (maximalIdeal R) R) t) = PowerSeries.X := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span.solution
