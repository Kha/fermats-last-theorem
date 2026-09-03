import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq

set_option autoImplicit false

theorem IsLocalRing.surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq
    {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (f : R →+* S) (hloc : ∀ r ∈ IsLocalRing.maximalIdeal R, f r ∈ IsLocalRing.maximalIdeal S)
    (hres : ∀ s : S, ∃ r : R, s - f r ∈ IsLocalRing.maximalIdeal S)
    (hcot : IsLocalRing.maximalIdeal S ≤
      (IsLocalRing.maximalIdeal R).map f ⊔ IsLocalRing.maximalIdeal S ^ 2) :
    Function.Surjective f := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq.solution
