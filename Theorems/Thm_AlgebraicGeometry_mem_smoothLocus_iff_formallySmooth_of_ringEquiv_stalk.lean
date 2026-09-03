import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (x : X) {S : Type} [CommRing S] [Algebra R S] (e : X.presheaf.stalk x ≃+* S)
    (he : ∀ r : R, e ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) =
      algebraMap R S r) :
    x ∈ f.smoothLocus ↔ Algebra.FormallySmooth R S := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk.solution
