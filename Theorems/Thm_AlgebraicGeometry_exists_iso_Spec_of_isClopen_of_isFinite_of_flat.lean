import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_Spec_of_isClopen_of_isFinite_of_flat
    {S : Type u} [CommRing S] {K : Scheme.{u}} (p : K ⟶ Spec (CommRingCat.of S)) [IsFinite p] [Flat p]
    (𝒢 : K.Opens) (h𝒢 : IsClosed (𝒢 : Set ↥K)) :
    ∃ (S' : Type u) (_ : CommRing S') (φ : S →+* S') (e : Spec (CommRingCat.of S') ≅ (𝒢 : Scheme.{u})),
      e.hom ≫ 𝒢.ι ≫ p = Spec.map (CommRingCat.ofHom φ) ∧
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧
      (Surjective (𝒢.ι ≫ p) → Surjective (Spec.map (CommRingCat.ofHom φ))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat.solution
