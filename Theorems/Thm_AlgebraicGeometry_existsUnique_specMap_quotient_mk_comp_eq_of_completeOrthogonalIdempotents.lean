import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_specMap_quotient_mk_comp_eq_of_completeOrthogonalIdempotents

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_specMap_quotient_mk_comp_eq_of_completeOrthogonalIdempotents
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {ι : Type} [Fintype ι] (e : ι → S) (he : CompleteOrthogonalIdempotents e)
    {N : Scheme.{u}} (gN : N ⟶ Spec (CommRingCat.of R))
    (φ : ∀ i : ι, Spec (CommRingCat.of (S ⧸ Ideal.span {1 - e i})) ⟶ N)
    (hφ : ∀ i, φ i ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R (S ⧸ Ideal.span {1 - e i})))) :
    ∃! Φ : Spec (CommRingCat.of S) ⟶ N,
      Φ ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R S)) ∧
      ∀ i, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e i}))) ≫ Φ = φ i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_specMap_quotient_mk_comp_eq_of_completeOrthogonalIdempotents.solution
