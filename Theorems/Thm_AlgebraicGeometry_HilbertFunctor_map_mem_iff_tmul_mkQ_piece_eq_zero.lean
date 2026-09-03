import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero

set_option autoImplicit false
open MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

theorem AlgebraicGeometry.HilbertFunctor.map_mem_iff_tmul_mkQ_piece_eq_zero
    (n : ℕ) (h : ℕ → ℕ) (B A : Type) [CommRing B] [CommRing A] (φ : B →+* A)
    (P : Point B n h) (Q : Point A n h) (hQ : Q.I = Ideal.map (MvPolynomial.map φ) P.I)
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) B) (hF : F.IsHomogeneous d) :
    MvPolynomial.map φ F ∈ Q.I ↔
      (letI : Algebra B A := φ.toAlgebra
       ((1 : A) ⊗ₜ[B] (Submodule.Quotient.mk ⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩ : piece P.I d) :
          A ⊗[B] piece P.I d) = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.solution
