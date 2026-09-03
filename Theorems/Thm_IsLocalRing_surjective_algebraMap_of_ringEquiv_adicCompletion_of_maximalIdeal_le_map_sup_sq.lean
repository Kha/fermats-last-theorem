import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_surjective_algebraMap_of_ringEquiv_adicCompletion_of_maximalIdeal_le_map_sup_sq

set_option autoImplicit false

theorem IsLocalRing.surjective_algebraMap_of_ringEquiv_adicCompletion_of_maximalIdeal_le_map_sup_sq
    {R S M : Type*} [CommRing R] [CommRing S] [CommRing M]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S] [IsNoetherianRing S] [IsLocalRing M] [IsNoetherianRing M]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    (hres : ∀ s : S, ∃ r : R, s - algebraMap R S r ∈ IsLocalRing.maximalIdeal S)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* M)
    (hcot : IsLocalRing.maximalIdeal M ≤
      (IsLocalRing.maximalIdeal R).map (ι.toRingHom.comp ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp
        (algebraMap R S))) ⊔ IsLocalRing.maximalIdeal M ^ 2) :
    Function.Surjective (algebraMap R S) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_surjective_algebraMap_of_ringEquiv_adicCompletion_of_maximalIdeal_le_map_sup_sq.solution
