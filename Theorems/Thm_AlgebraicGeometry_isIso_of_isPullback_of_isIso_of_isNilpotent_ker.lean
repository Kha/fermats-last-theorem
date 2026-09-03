import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIso_of_isPullback_of_isIso_of_isNilpotent_ker
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {X Y X₀ Y₀ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of T')) (q : Y ⟶ Spec (CommRingCat.of T'))
    [Flat p] [LocallyOfFinitePresentation p] [Flat q] [LocallyOfFinitePresentation q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (p₀ : X₀ ⟶ Spec (CommRingCat.of T)) (q₀ : Y₀ ⟶ Spec (CommRingCat.of T))
    (gX : X₀ ⟶ X) (hX : IsPullback gX p₀ p (Spec.map (CommRingCat.ofHom π)))
    (gY : Y₀ ⟶ Y) (hY : IsPullback gY q₀ q (Spec.map (CommRingCat.ofHom π)))
    (φ₀ : X₀ ⟶ Y₀) (hφ₀ : φ₀ ≫ gY = gX ≫ φ) (hφ₀q : φ₀ ≫ q₀ = p₀) [IsIso φ₀] :
    IsIso φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker.solution
