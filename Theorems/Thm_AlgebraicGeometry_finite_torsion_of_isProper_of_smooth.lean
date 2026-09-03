import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_torsion_of_isProper_of_smooth

open CategoryTheory

theorem AlgebraicGeometry.finite_torsion_of_isProper_of_smooth
    (K : Type*) [Field K] [IsAlgClosed K]
    (J : AlgebraicGeometry.Scheme)
    (c : J ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (hsm : AlgebraicGeometry.Smooth c)
    (hpr : AlgebraicGeometry.IsProper c)
    (mul : CategoryTheory.Limits.pullback c c ⟶ J)
    (G : Type*) [AddCommGroup G]
    (pts : G ≃ {σ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ J // σ ≫ c = 𝟙 _})
    (hadd : ∀ x y : G, (pts (x + y)).1 =
      CategoryTheory.Limits.pullback.lift (pts x).1 (pts y).1
        ((pts x).2.trans (pts y).2.symm) ≫ mul)
    (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite {x : G // n • x = 0} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_torsion_of_isProper_of_smooth.solution
