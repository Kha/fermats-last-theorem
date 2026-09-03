import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [IsProper fX] [IsSeparated fY]
    (g : ℕ) [SmoothOfRelativeDimension g fX] [SmoothOfRelativeDimension g fY]
    (φ : X ⟶ Y) (hφ : φ ≫ fY = fX) [LocallyQuasiFinite φ] :
    IsFinite φ ∧ Flat φ ∧ Surjective φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension.solution
