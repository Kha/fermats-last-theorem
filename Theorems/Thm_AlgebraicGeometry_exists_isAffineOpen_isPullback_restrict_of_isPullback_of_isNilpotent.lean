import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding isAffine_of_isClosedImmersion_of_surjective

universe u

theorem AlgebraicGeometry.exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {W Q : Scheme.{u}} (q : Q ⟶ Spec (CommRingCat.of T')) (w : W ⟶ Spec (CommRingCat.of T)) (G : W ⟶ Q)
    (hG : IsPullback G w q (Spec.map (CommRingCat.ofHom π)))
    (V : W.Opens) (hV : IsAffineOpen V) :
    ∃ (Z : Q.Opens) (_ : IsAffineOpen Z) (γ : (↑V : Scheme.{u}) ⟶ ↑Z),
      γ ≫ Z.ι = V.ι ≫ G ∧ IsPullback γ (V.ι ≫ w) (Z.ι ≫ q) (Spec.map (CommRingCat.ofHom π)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent.solution
