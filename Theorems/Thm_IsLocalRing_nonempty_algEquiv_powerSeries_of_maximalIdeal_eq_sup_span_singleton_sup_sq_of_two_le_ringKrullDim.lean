import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim

set_option autoImplicit false

theorem IsLocalRing.nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (t : R)
    (ht : IsLocalRing.maximalIdeal R =
      (IsLocalRing.maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span {t} ⊔ (IsLocalRing.maximalIdeal R) ^ 2)
    (hdim : 2 ≤ ringKrullDim R) :
    Nonempty (R ≃ₐ[O] PowerSeries O) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim.solution
