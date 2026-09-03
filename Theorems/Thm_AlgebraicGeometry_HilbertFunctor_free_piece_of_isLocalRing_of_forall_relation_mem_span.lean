import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.free_piece_of_isLocalRing_of_forall_relation_mem_span
    (n m g : ℕ) (A : Type) [CommRing A] [IsLocalRing A]
    (F : Fin g → MvPolynomial (Fin (n + 1)) A) (hF : ∀ i, (F i).IsHomogeneous m)
    (h₀ : Module.Projective A (piece (Ideal.span (Set.range F)) m))
    (h₁ : Module.Projective A (piece (Ideal.span (Set.range F)) (m + 1)))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A)),
      (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0 →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A))
        {l : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A) |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧
          ∑ i, l i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0}) :
    ∀ e, Module.Free A (piece (Ideal.span (Set.range F)) e) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span.solution
