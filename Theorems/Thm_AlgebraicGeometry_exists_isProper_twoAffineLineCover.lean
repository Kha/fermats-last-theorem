import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem AlgebraicGeometry.exists_isProper_twoAffineLineCover (S : Type u) [CommRing S] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of S)) (i₀ i₁ : Spec (CommRingCat.of (Polynomial S)) ⟶ P),
      IsProper p ∧ IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      i₀ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      i₁ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) ≫ i₁ ∧
      IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))
        (Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))) i₀ i₁ ∧
      (IsDomain S → IsIntegral P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover.solution
