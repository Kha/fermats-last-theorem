import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.GrpObj.mul_eq_of_one_eq
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced (CategoryTheory.Limits.pullback x x)]
    (G₁ G₂ : GrpObj (Over.mk x)) (h : G₁.one = G₂.one) : G₁.mul = G₂.mul := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq.solution
