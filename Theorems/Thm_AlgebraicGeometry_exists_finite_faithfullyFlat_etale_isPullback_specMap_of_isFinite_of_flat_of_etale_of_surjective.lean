import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective"
open scoped TensorProduct

theorem AlgebraicGeometry.exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective
    {H M : Scheme.{u}} (q : H ⟶ M) [IsFinite q] [Flat q] [Etale q] (hqsurj : Function.Surjective q.base)
    {S : Type u} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ M) :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.Finite S S' ∧ Module.FaithfullyFlat S S' ∧ Algebra.Etale S S' ∧
      ∃ y : Spec (CommRingCat.of S') ⟶ H, IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S S'))) y x q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective.solution
