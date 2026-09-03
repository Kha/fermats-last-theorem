import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.surjective_specMap_of_surjective_of_ker_le_nilradical
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical R) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical.solution
