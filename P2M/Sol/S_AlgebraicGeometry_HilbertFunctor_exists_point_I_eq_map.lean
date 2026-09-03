import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem solution
    (n : ℕ) (h : ℕ → ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Point A n h) :
    ∃ Q : Point B n h, Q.I = P.I.map (MvPolynomial.map (algebraMap A B)) := by
  obtain ⟨hhom, hpiece⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n A B P.I P.homogeneous
  have hfin : ∀ d, Module.Finite B (piece (P.I.map (MvPolynomial.map (algebraMap A B))) d) := by
    intro d
    obtain ⟨e, -⟩ := hpiece d
    haveI := P.finite_piece d
    exact Module.Finite.equiv e
  have hproj : ∀ d, Module.Projective B (piece (P.I.map (MvPolynomial.map (algebraMap A B))) d) := by
    intro d
    obtain ⟨e, -⟩ := hpiece d
    haveI := P.projective_piece d
    haveI : Module.Projective B (B ⊗[A] piece P.I d) := Module.Projective.tensorProduct
    exact Module.Projective.of_equiv e
  have hrank : ∀ (d : ℕ) (q : PrimeSpectrum B),
      Module.rankAtStalk (piece (P.I.map (MvPolynomial.map (algebraMap A B))) d) q = h d := by
    intro d q
    obtain ⟨e, -⟩ := hpiece d
    haveI := P.finite_piece d
    haveI := P.projective_piece d
    rw [← congrArg (fun g => g q) (Module.rankAtStalk_eq_of_equiv e), Module.rankAtStalk_baseChange,
      P.rankAtStalk_piece]
  exact ⟨{ I := P.I.map (MvPolynomial.map (algebraMap A B))
           homogeneous := hhom
           finite_piece := hfin
           projective_piece := hproj
           rankAtStalk_piece := hrank }, rfl⟩
