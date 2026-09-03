import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic"

theorem AlgebraicGeometry.exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    {X Y X₀ Y₀ : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of K))
    (fX₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) (fY₀ : Y₀ ⟶ Spec (CommRingCat.of ↥L))
    [CompactSpace ↥X₀] [QuasiSeparatedSpace ↥X₀] [LocallyOfFiniteType fY₀]
    (gX : X ⟶ X₀) (hgX : IsPullback gX fX fX₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K))))
    (gY : Y ⟶ Y₀) (hgY : IsPullback gY fY fY₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K))))
    (φ : X ⟶ Y) (hφ : φ ≫ fY = fX) :
    ∃ (Lφ : IntermediateField k K) (_ : FiniteDimensional k ↥Lφ) (_ : L ≤ Lφ),
      ∀ (L'' : IntermediateField k K) (_ : Lφ ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ Y₂ : Scheme.{0}) (fX₂ : X₂ ⟶ Spec (CommRingCat.of ↥L'')) (fY₂ : Y₂ ⟶ Spec (CommRingCat.of ↥L''))
        (rX : X ⟶ X₂) (_ : IsPullback rX fX fX₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (qX : X₂ ⟶ X₀) (_ : IsPullback qX fX₂ fX₀ (Spec.map (CommRingCat.ofHom j))) (_ : rX ≫ qX = gX)
        (rY : Y ⟶ Y₂) (_ : IsPullback rY fY fY₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (qY : Y₂ ⟶ Y₀) (_ : IsPullback qY fY₂ fY₀ (Spec.map (CommRingCat.ofHom j))) (_ : rY ≫ qY = gY),
        ∃ φ₂ : X₂ ⟶ Y₂, φ₂ ≫ fY₂ = fX₂ ∧ rX ≫ φ₂ = φ ≫ rY := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic.solution
