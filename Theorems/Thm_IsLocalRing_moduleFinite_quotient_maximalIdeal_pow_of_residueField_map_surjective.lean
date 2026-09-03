import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective

set_option autoImplicit false

theorem IsLocalRing.moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S))) (k : ℕ) :
    Module.Finite R (S ⧸ IsLocalRing.maximalIdeal S ^ k) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective.solution
