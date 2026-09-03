import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (H : ∀ (ι : Type u) [Finite ι], IsClosedMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))).base) :
    UniversallyClosed f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.solution
