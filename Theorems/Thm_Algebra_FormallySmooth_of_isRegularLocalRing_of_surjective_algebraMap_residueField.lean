import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_of_isRegularLocalRing_of_surjective_algebraMap_residueField

set_option autoImplicit false

universe u

open IsLocalRing

theorem Algebra.FormallySmooth.of_isRegularLocalRing_of_surjective_algebraMap_residueField
    (k : Type u) [Field k] (S : Type u) [CommRing S] [IsRegularLocalRing S]
    [Algebra k S] [Algebra.EssFiniteType k S]
    (hk : Function.Surjective (algebraMap k (ResidueField S))) :
    Algebra.FormallySmooth k S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_of_isRegularLocalRing_of_surjective_algebraMap_residueField.solution
