import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsPullback_surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsPullback.surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (D : P.Opens) (hD : IsAffineOpen D) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p D
    Function.Surjective (G.app D).hom ∧
      RingHom.ker (G.app D).hom = (RingHom.ker π).map (algebraMap T' Γ(P, D)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsPullback_surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen.solution
