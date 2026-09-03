import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k))
    (U : (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens)
    (hU : IsCompact (U : Set ↥(pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)

      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (V : (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).Opens),
      IsCompact (V : Set ↥(pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧

      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
          (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ⁻¹ᵁ V = U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.solution
