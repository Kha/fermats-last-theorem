import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegrallyClosed_stalk_of_mem_smoothLocus

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegrallyClosed_stalk_of_mem_smoothLocus
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (y : X) (hy : y ∈ f.smoothLocus) : IsIntegrallyClosed (X.presheaf.stalk y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegrallyClosed_stalk_of_mem_smoothLocus.solution
