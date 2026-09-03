import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem AlgebraicGeometry.exists_toLaurent_comp_eq_of_isProper {k : Type u} [Field k] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (CommRingCat.of k)) [IsProper fZ]
    (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Z)
    (hφ : φ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ ψ : Spec (CommRingCat.of (Polynomial k)) ⟶ Z,
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k)) ≫ ψ = φ ∧
      ψ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper.solution
