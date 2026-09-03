import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_projective_piece_succ_iff

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_projective_piece_succ_iff
    (n m q r : ℕ)
    (hmax : ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s) →
      Module.finrank K (piece J m) = q → Module.finrank K (piece J (m + 1)) ≤ r)
    (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous m) ∧ I = Ideal.span s)
    (hproj : Module.Projective A (piece I m))
    (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece I m) p = q) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra A B],
      (Module.Projective B (piece (I.map (MvPolynomial.map (algebraMap A B))) (m + 1)) ∧
        ∀ 𝔮 : PrimeSpectrum B,
          Module.rankAtStalk (piece (I.map (MvPolynomial.map (algebraMap A B))) (m + 1)) 𝔮 = r) ↔
      ∀ a ∈ 𝔞, algebraMap A B a = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_projective_piece_succ_iff.solution
