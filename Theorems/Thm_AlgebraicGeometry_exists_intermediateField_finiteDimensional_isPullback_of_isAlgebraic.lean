import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic~exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic"

theorem AlgebraicGeometry.exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX] :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Spec (CommRingCat.of L)) (_ : CompactSpace X₀) (_ : QuasiSeparatedSpace X₀)
      (_ : LocallyOfFiniteType f₀) (g : X ⟶ X₀),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap L K))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.solution
