import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import P2M.Util
namespace P2MW.S_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [IsReduced R] [IsNoetherianRing R] : IsReduced S := by
  have hsm : AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
    show (algebraMap R S).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance
  have := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact (affine_isReduced_iff (CommRingCat.of S)).mp this
