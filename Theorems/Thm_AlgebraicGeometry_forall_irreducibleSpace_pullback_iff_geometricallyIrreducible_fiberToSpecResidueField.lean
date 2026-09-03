import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed"

universe u

theorem AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) (s : ↥(Spec (CommRingCat.of S))) :
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField.solution
