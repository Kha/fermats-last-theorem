import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing
set_option autoImplicit false

theorem AdicCompletion.ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (e₁ e₂ : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (h : ∀ r : R, e₁ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)
      = e₂ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)) :
    e₁ = e₂ := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing.solution
