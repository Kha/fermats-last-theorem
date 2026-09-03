import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import P2M.Util
import P2M.Sol.S_AdicCompletion_ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type*} [CommRing T] [IsLocalRing T] [IsHausdorff (maximalIdeal T) T]
    (g₁ g₂ : AdicCompletion (maximalIdeal R) R →+* T)
    (hg₁ : ∀ x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), g₁ x ∈ maximalIdeal T)
    (hg₂ : ∀ x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), g₂ x ∈ maximalIdeal T)
    (h : ∀ r : R, g₁ (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      g₂ (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) :
    g₁ = g₂ := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq.solution
