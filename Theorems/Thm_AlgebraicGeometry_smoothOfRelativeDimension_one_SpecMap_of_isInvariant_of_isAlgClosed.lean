import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
    {k S A : Type u} [Field k] [IsAlgClosed k] [CommRing S] [CommRing A]
    [Algebra k S] [Algebra k A] [Algebra S A] [IsScalarTower k S A] [FaithfulSMul S A]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G k A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed.solution
