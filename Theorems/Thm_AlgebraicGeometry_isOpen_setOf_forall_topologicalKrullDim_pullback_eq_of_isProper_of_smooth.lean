import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~smoothOfRelativeDimension_of_irreducibleSpace"

universe u

theorem AlgebraicGeometry.isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f]
    (hirr : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (g : ℕ) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth.solution
