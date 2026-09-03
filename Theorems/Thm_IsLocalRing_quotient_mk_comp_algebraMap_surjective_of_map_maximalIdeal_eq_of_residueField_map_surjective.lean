import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_quotient_mk_comp_algebraMap_surjective_of_map_maximalIdeal_eq_of_residueField_map_surjective

set_option autoImplicit false

theorem IsLocalRing.quotient_mk_comp_algebraMap_surjective_of_map_maximalIdeal_eq_of_residueField_map_surjective
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S))) (k : ℕ) :
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal S ^ k)).comp (algebraMap R S)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_quotient_mk_comp_algebraMap_surjective_of_map_maximalIdeal_eq_of_residueField_map_surjective.solution
